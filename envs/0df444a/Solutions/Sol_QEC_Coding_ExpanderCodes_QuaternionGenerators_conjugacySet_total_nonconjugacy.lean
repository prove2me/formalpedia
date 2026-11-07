-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugacySet_total_nonconjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:59.095209+00:00
-- url     : https://prove2.me/submissions/2605ee8e-2d2d-45d6-91d3-3f301bde4435

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugate_sq_ne_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mul_ne_mul_of_separated_squares
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
variable {H : Type*} [Group H]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (T U : Subgroup H) (a b : H)
    (ha : a ^ 2 ≠ 1) (hb : b ^ 2 = 1)
    {x y : H} (hx : x ∈ conjugacySet T a) (hy : y ∈ conjugacySet U b) (g : H) :
    x * g ≠ g * y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  apply mul_ne_mul_of_separated_squares
  · exact conjugate_sq_ne_one a s ha
  · rw [conj_pow, hb]
    simp
end QEC.Coding.ExpanderCodes.QuaternionGenerators
