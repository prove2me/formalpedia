-- Prove2me | solution 1 for PetersenTheorem.outDarts_add_innDarts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:43.977944+00:00
-- url     : https://prove2.me/submissions/3bdda47a-9bc4-4303-bd88-dc56e0a323e9

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace PetersenTheorem
theorem _root_.solution (h3 : G.IsRegularOfDegree 3) (C : Finset V) :
    outDarts G C + innDarts G C = 3 * C.card := by
  unfold outDarts innDarts
  rw [← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_sdiff_add_card_inter, card_neighborFinset_eq_degree, h3 x]
  rfl
end PetersenTheorem
