-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.inv_mem_conjugacySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:11.326195+00:00
-- url     : https://prove2.me/submissions/3bcd9624-db77-44e5-bcf4-1165e39e9c75

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
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
theorem _root_.solution (T : Subgroup H) (a u : H) (hu : u ∈ T)
    (hInverse : u * a * u⁻¹ = a⁻¹) {g : H} (hg : g ∈ conjugacySet T a) :
    g⁻¹ ∈ conjugacySet T a := by
  obtain ⟨t, rfl⟩ := hg
  refine ⟨t * ⟨u, hu⟩, ?_⟩
  change ((t : H) * u) * a * ((t : H) * u)⁻¹ =
    ((t : H) * a * (t : H)⁻¹)⁻¹
  calc
    _ = (t : H) * (u * a * u⁻¹) * (t : H)⁻¹ := by simp [mul_assoc]
    _ = (t : H) * a⁻¹ * (t : H)⁻¹ := by rw [hInverse]
    _ = _ := by simp [mul_assoc]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
