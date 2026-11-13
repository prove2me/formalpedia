-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.groupObjectsInCatAreGroupoids
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:38:54.057067+00:00
-- url     : https://prove2.me/submissions/cc52e908-d204-4e88-a30a-76cc2e2fe539

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGrpAndGroupCat
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGroup_composition_formula
import Mathlib.Tactic.Group
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 12, the Brown-Spencer strengthening as explicitly stated in this
paper: every arrow of a strict group object in Cat has a two-sided categorical
inverse. This is categorical inversion, distinct from the ambient group inverse.
Together with the two structure correspondences above, this gives the stated
crossed-module correspondence with group objects in Grpd. The source supplies
no further hypothesis and does not require its cited proof as input. -/
theorem solution {A : Type u} {O : Type v}
    [Group A] [Group O] (D : CategoryMaps A O) (h : GroupObjectInCat D) :
    ∀ f : A, ∃ g : A,
      D.source g = D.target f ∧ D.target g = D.source f ∧
      D.compose g f = D.identity (D.source f) ∧
      D.compose f g = D.identity (D.target f) := by
  have hi : InternalCategoryInGrp D := (internalGrpAndGroupCat D).mpr h
  intro f
  let g := D.identity (D.source f) * f⁻¹ * D.identity (D.target f)
  have hs : D.source g = D.target f := by
    dsimp [g]
    rw [hi.source_mul,hi.source_mul,hi.category.source_identity,hi.category.source_identity]
    have hh := (sourceHom D hi).map_inv f
    change D.source f⁻¹ = (D.source f)⁻¹ at hh
    rw [hh,mul_inv_cancel,one_mul]
  have ht : D.target g = D.source f := by
    dsimp [g]
    rw [hi.target_mul,hi.target_mul,hi.category.target_identity,hi.category.target_identity]
    have hh := (targetHom D hi).map_inv f
    change D.target f⁻¹ = (D.target f)⁻¹ at hh
    rw [hh,mul_assoc,inv_mul_cancel,mul_one]
  refine ⟨g,hs,ht,?_,?_⟩
  · rw [internalGroup_composition_formula D hi f g hs.symm,hs]
    dsimp [g]
    group
  · rw [internalGroup_composition_formula D hi g f ht]
    dsimp [g]
    group
