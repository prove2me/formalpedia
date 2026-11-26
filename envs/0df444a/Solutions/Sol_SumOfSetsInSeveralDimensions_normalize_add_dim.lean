-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.normalize_add_dim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:08.1858+00:00
-- url     : https://prove2.me/submissions/e04b0956-1a50-4555-9b0e-3b9841c9d567

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_image_sub
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
private lemma normalize_add {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    normalize A hA + normalize B hB =
      (A + B).image fun x ↦ x - (lexMin A hA + lexMin B hB) := by
  ext x
  simp only [normalize, mem_add, mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a - lexMin A hA, ⟨a, ha, rfl⟩, b - lexMin B hB, ⟨b, hb, rfl⟩, by abel⟩
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
theorem _root_.solution {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    (normalize A hA + normalize B hB).affineDim = (A + B).affineDim := by
  rw [normalize_add, affineDim_image_sub]
end SumOfSetsInSeveralDimensions
