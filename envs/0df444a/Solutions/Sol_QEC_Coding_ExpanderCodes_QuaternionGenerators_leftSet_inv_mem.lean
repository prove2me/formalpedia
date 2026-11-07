-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:42.500235+00:00
-- url     : https://prove2.me/submissions/8fd0c983-2225-4354-b412-7702988035ea

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_conjugate_base
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_mem_quadraticTorus
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) {g : ProjectiveGroup epsilon y}
    (hg : g ∈ leftSet epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ leftSet epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet _ _ _ (projectiveAlpha_mem_quadraticTorus epsilon y hEpsilon)
    (projectiveAlpha_conjugate_base epsilon y hEpsilon hY hOne) hg
end QEC.Coding.ExpanderCodes.QuaternionGenerators
