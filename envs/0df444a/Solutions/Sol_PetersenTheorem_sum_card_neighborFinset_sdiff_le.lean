-- Prove2me | solution 1 for PetersenTheorem.sum_card_neighborFinset_sdiff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:13:09.607316+00:00
-- url     : https://prove2.me/submissions/f00e4d44-15b8-4673-a62d-e25786c34e87

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
namespace PetersenTheorem
theorem _root_.solution [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (T : Finset V) :
    ∑ y ∈ T, (G.neighborFinset y \ T).card ≤ 3 * T.card := by
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun y _ => (Finset.card_le_card Finset.sdiff_subset).trans ?_
  rw [card_neighborFinset_eq_degree, h3 y]
end PetersenTheorem
