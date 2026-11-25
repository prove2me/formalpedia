-- Prove2me | solution 1 for RegularSubgraph.totalDegree_poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:22:36.166076+00:00
-- url     : https://prove2.me/submissions/a1628e16-6f9b-4877-a68a-0396557065ee

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
variable [hp : Fact p.Prime]
namespace RegularSubgraph
theorem _root_.solution (v : V) : (poly G p v).totalDegree ≤ p - 1 := by
  unfold poly
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun w _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have : (var G p v w).totalDegree ≤ 1 := by
    unfold var
    split_ifs
    · exact (totalDegree_X _).le
    · simp
  calc (p - 1) * (var G p v w).totalDegree ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ this
    _ = p - 1 := mul_one _
end RegularSubgraph
