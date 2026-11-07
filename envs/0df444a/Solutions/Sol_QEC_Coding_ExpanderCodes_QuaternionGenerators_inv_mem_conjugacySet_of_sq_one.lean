-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.inv_mem_conjugacySet_of_sq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:58.198253+00:00
-- url     : https://prove2.me/submissions/9c024261-07fe-450d-8cea-aa1c77f7fb41

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet
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
theorem _root_.solution (T : Subgroup H) (a : H)
    (hSquare : a ^ 2 = 1) {g : H} (hg : g ∈ conjugacySet T a) :
    g⁻¹ ∈ conjugacySet T a := by
  apply inv_mem_conjugacySet T a 1 T.one_mem _ hg
  simpa using (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hSquare)).symm
end QEC.Coding.ExpanderCodes.QuaternionGenerators
