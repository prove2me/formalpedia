-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_mem_quadraticTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:19.2346+00:00
-- url     : https://prove2.me/submissions/88b2fd43-a3c2-4014-b942-cc1029cd3dc9

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
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K)
    (hEpsilon : epsilon ≠ 0) :
    projectiveAlpha epsilon y hEpsilon ∈ quadraticTorus epsilon y hEpsilon := by
  refine ⟨alphaUnit epsilon y hEpsilon, ?_, rfl⟩
  simp [Subgroup.mem_centralizer_iff]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
