use std::collections::HashMap;

use crate::{AssistContext, Assists};
use ide_db::assists::{AssistId, AssistKind};
use itertools::Itertools;
use syntax::{
    ast::{self, vst::*},
    AstNode,
};


/// This proof action will: 
/// 1. Find the variables in require clause that remains during the whole function.
/// 2. Add the "invariables" to the invariants of any loops in this function.
/// It is triggerd on `requires` keyword.
pub(crate) fn add_const_to_invs(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // setup basic variables
    let func: ast::Fn = ctx.find_node_at_offset::<ast::Fn>()?;
    let body: ast::BlockExpr = func.body()?;
    let requires: ast::RequiresClause = func.requires_clause()?;

    // trigger on "requires"
    // check if cursor is on "requires" keyword
    let requires_keyword = requires.requires_token()?;
    let cursor_in_range = requires_keyword.text_range().contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    let requires_expr = requires
        .exprs().collect::<Vec<_>>();

    let v_body = BlockExpr::try_from(body.clone()).ok()?;
    let result = vst_rewriter_add_const_to_invs(ctx, v_body.clone(), &requires_expr)?;
    let result = ctx.fmt(body.clone(), result.to_string())?;

    acc.add(
        AssistId("add_const_to_invs", AssistKind::RefactorRewrite),
        "Add const to invariants of loops in this function",
        body.syntax().text_range(),
        |edit| {
            edit.replace(body.syntax().text_range(), result);
        },
    )
}


/// Rewrites the body of a function to add a "invariable" to the invariants of loops.
/// It finds the variables in the `requires` clause that remain constant throughout the function,
/// and adds them to the invariants of any loops in this function.
fn vst_rewriter_add_const_to_invs(
    ctx: &AssistContext<'_>,
    mut blk: BlockExpr,
    require_exprs: &Vec<ast::Expr>,
) -> Option<BlockExpr> {
    // Find the variables in the requires clause that remain constant throughout the function
    // inv_vars[expr] = true => remain invariant in this function.
    // inv_vars[expr] = false => not invariant in this function.
    // !Simple keep the Literal Exprs right now.
    let mut inv_vars = require_exprs
        .iter()
        .filter_map(|expr| {
            if let ast::Expr::Literal(lit) = expr {
                Some((lit.clone(), true)) // Assume all literals are invariant for now
            } else {
                None // Ignore non-literal expressions for now
            }
        })
        .collect::<HashMap<_, _>>();

    // Walk through the whole body of the function
    // Find whether all the invars in the requires clause remain constant.
    // That means, if any stmt will change the value of the variable,
    // check whether it is in `inv_vars` or not.
    // If it is, set it to false, otherwise, keep it true.
    for stmt in blk.stmt_list.statements.iter() {
        match stmt {
            Stmt::ExprStmt(expr_stmt) => {
                
            }
            Stmt::Item(item) => {
                
            }
            _ => {}
        }
    }

    Some(blk)
    
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::check_assist;

    #[test]
    fn test_add_const_to_invs() {
        check_assist(
            add_const_to_invs,
            r#"
            fn foo()
                requires x == 42;
            {
                loop
                {
                    // some code
                }
            }
            "#,
            r#"
            fn foo()
                requires x == 42;
            {
                loop
                    invariant x == 42; // Added invariant
                {
                    // some code
                }
            }
            "#,
        );
    }
}