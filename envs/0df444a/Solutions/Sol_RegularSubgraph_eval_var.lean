-- Prove2me | solution 1 for RegularSubgraph.eval_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:33.224967+00:00
-- url     : https://prove2.me/submissions/f9f6d2a0-9e49-4c1f-8cc2-4251c4004792

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
variable {G p}
omit [Fintype V]
namespace RegularSubgraph
theorem _root_.solution (x : Edge G → ZMod p) (a b : V) : eval x (var G p a b) = val G p x a b := by
  unfold var val
  split_ifs <;> simp
end RegularSubgraph
