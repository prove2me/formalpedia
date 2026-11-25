-- Prove2me | solution 1 for RegularSubgraph.eval_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:25:34.22358+00:00
-- url     : https://prove2.me/submissions/0ed72f5b-4f67-48f8-bfc2-43edd9741a2e

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Theorems.Thm_RegularSubgraph_eval_var

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ)
variable {G p}
variable [hp : Fact p.Prime]
namespace RegularSubgraph
theorem _root_.solution (x : Edge G → ZMod p) (v : V) :
    eval x (poly G p v) = (#{w | val G p x v w ≠ 0} : ℕ) := by
  unfold poly
  rw [map_sum, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_pow, eval_var]
  by_cases h : val G p x v w = 0
  · simp [h, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)]
  · simp [ZMod.pow_card_sub_one_eq_one h, h]
end RegularSubgraph
