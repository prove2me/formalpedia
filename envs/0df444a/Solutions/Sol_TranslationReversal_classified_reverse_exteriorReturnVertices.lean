-- Prove2me | solution 1 for TranslationReversal.classified_reverse_exteriorReturnVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:49.391468+00:00
-- url     : https://prove2.me/submissions/649268cc-6125-47a7-b7e0-e998e3be1af9

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_TranslationReversal_classified_reverse_interior_head

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationReversal
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationReversal.graphAdjDecidable
attribute [local instance] TranslationReversal.vertexDecidableEq
namespace TranslationReversal
theorem _root_.solution (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    exteriorReturnVertices (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      exteriorReturnVertices (d := d) G hG start rho k q := by
  classical
  let c := returnLength d G hG start rho k q
  unfold exteriorReturnVertices interiorRouteVertices
  rw [classified_reverse_returnLength (d := d) G hG start rho k q q' hend]
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨t, ht, htv⟩ := Finset.mem_image.mp hv
    have ht0 : 0 < t := (Finset.mem_Ico.mp ht).1
    have htc : t < c := (Finset.mem_Ico.mp ht).2
    apply Finset.mem_image.mpr
    refine ⟨c - t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [← htv]
    exact (classified_reverse_interior_head (d := d) G hG start rho k q q'
      hend t ht0 htc).symm
  · intro v hv
    obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hv
    have hs0 : 0 < s := (Finset.mem_Ico.mp hs).1
    have hsc : s < c := (Finset.mem_Ico.mp hs).2
    apply Finset.mem_image.mpr
    refine ⟨c - s, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hhead := classified_reverse_interior_head (d := d) G hG start rho k q
      q' hend (c - s) (by omega) (by omega)
    rw [show c - (c - s) = s by omega] at hhead
    exact hhead.trans hsv
end TranslationReversal
