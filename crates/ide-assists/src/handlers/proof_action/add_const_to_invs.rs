use std::collections::HashMap;

use crate::{AssistContext, Assists};
use ide_db::assists::{AssistId, AssistKind};
use itertools::Itertools;
use syntax::{
    ast::{self, edit::AstNodeEdit, vst::*}, AstNode, AstToken, SyntaxKind
};

///! Do not use it right now. Let it be a placeholder for future use.


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
    println!("Requires expressions: {:#?}", requires_expr);

    let v_body = BlockExpr::try_from(body.clone()).ok()?;

    let result = vst_rewriter_add_const_to_invs(ctx, v_body.clone(), &requires_expr)?;
    let result = ctx.fmt(body.clone(), result.to_string())?;

   
    acc.add(
        AssistId("add_const_to_invs", AssistKind::RefactorRewrite),
        "Add const to invariants of loops in this function",
        func.syntax().text_range(),
        |edit| {
            edit.replace(func.syntax().text_range(), result);
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
    // !Simply keeps the Ident Exprs right now.
    let mut inv_vars: HashMap<String, Vec<ast::Expr>> = HashMap::new();

    for expr in require_exprs {
        let idents = find_idents_in_expr(expr);
        println!("\n\n");
        if !idents.is_empty() {
            for ident in idents {
                // Store the identifier and the expression in the inv_vars map.
                // Some(...) means it is invariant.
                if let Some(existing_exprs) = inv_vars.get_mut(&ident.to_string()) {
                    existing_exprs.push(expr.clone());
                } else {
                    inv_vars.insert(ident.to_string(), vec![expr.clone()]);
                }
            }
        }
    }
    println!("Invariants found: {:#?}", inv_vars);

    // Walk through the whole body of the function
    // Find whether all the invars in the requires clause remain constant.
    // That means, if any stmt will change the value of the variable,
    // check whether it is in `inv_vars` or not.
    // If it is, set it to false, otherwise, keep it true.
    

    println!("Invariants after processing body: {:#?}", inv_vars);

    Some(blk)
    
}

/// Find all identifiers in an expression.
fn find_idents_in_expr(expr: &ast::Expr) -> Vec<ast::Ident> {
    let mut idents = Vec::new();
    let mut should_clear: bool = false;
    println!("Finding identifiers in expression: {:?}", expr);
    expr.syntax().descendants_with_tokens().for_each(|element| {
        if let Some(token) = element.as_token() {
            if token.kind() == SyntaxKind::IDENT {
                if let Some(ident) = ast::Ident::cast(token.clone()) {
                    println!("Found identifier: {:?}", ident);
                    idents.push(ident);
                }
            }
        } else {
            if element.kind() == SyntaxKind::CALL_EXPR {
                // If we encounter a call expression, we should clear the idents.
                should_clear = true;
            }
            println!("Not a token: {:?}", element.kind());
        }
    });
    if should_clear {
        idents.clear(); // Clear idents if we encountered a call expression
    }
    println!("Identifiers found: {:?}", idents);
    idents
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
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	req$0uires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
        
{
    sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
	    invariant
	        0 <= i <= N as usize,
	        a.len() == N as usize,
	        b.len() == N as usize,
	        sum.len() == 1,
	        forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}
}
            "#,
            r#"
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
{
    sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
	    invariant
	        0 <= i <= N as usize,
	        a.len() == N as usize,
	        b.len() == N as usize,
	        sum.len() == 1,
	        forall |k:int| 0 <= k < i ==> a[k] == 1,
            N > 0,
            N < 1000,
	{
		a.set(i, 1);
		i = i + 1;
	}
}
            "#,
        );
    }
}