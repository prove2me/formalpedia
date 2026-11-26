-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.normalize_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:39.660257+00:00
-- url     : https://prove2.me/submissions/7d606ca2-c706-41c3-a174-caa23b5c21ee

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset


section
public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
private lemma lexMin_le {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) {x : Fin D → ℝ}
    (hx : x ∈ S) : toLex (lexMin S hS) ≤ toLex x := by
  rw [lexMin, toLex_ofLex]
  exact min'_le _ _ (mem_image_of_mem toLex hx)
private lemma lexMin_sub_pos {S : Finset (Fin D → ℝ)} (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ S) (hne : x ≠ lexMin S hS) :
    0 < toLex (x - lexMin S hS) := by
  rw [toLex_sub, sub_pos]
  apply (lexMin_le hS hx).lt_of_ne
  simpa using hne.symm
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {S : Finset (Fin D → ℝ)} (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ normalize S hS) (hx0 : x ≠ 0) : 0 < toLex x := by
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
  apply lexMin_sub_pos hS hy
  rintro rfl
  exact hx0 (sub_self _)
end SumOfSetsInSeveralDimensions
