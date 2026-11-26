-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.normalize_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:41.299591+00:00
-- url     : https://prove2.me/submissions/9479f6ad-0878-4ddc-b991-96bfc75df3bf

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
    #(normalize A hA + normalize B hB) = #(A + B) := by
  rw [normalize_add]
  exact card_image_of_injective _ sub_left_injective
end SumOfSetsInSeveralDimensions
