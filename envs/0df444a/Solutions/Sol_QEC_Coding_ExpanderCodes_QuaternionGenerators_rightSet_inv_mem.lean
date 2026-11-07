-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.rightSet_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:47.366763+00:00
-- url     : https://prove2.me/submissions/8166493e-e510-4e63-af00-a87ab0691f10

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet_of_sq_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) {g : ProjectiveGroup epsilon y}
    (hg : g ∈ rightSet epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ rightSet epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet_of_sq_one _ _
    (projectivePrime_sq epsilon y hEpsilon hY hOne) hg
end QEC.Coding.ExpanderCodes.QuaternionGenerators
