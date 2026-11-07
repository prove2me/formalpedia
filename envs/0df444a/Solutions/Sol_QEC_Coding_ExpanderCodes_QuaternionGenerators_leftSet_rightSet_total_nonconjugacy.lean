-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.leftSet_rightSet_total_nonconjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:48.407771+00:00
-- url     : https://prove2.me/submissions/5b74ccfd-3293-4126-a9ab-677ef14aa107

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugacySet_total_nonconjugacy
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveBase_sq_ne_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup epsilon y}
    (ha : a ∈ leftSet epsilon y hEpsilon hY hOne)
    (hb : b ∈ rightSet epsilon y hEpsilon hY hOne) (g : ProjectiveGroup epsilon y) :
    a * g ≠ g * b :=
  conjugacySet_total_nonconjugacy _ _ _ _
    (projectiveBase_sq_ne_one epsilon y hEpsilon hY hOne hTwo)
    (projectivePrime_sq epsilon y hEpsilon hY hOne) ha hb g
end QEC.Coding.ExpanderCodes.QuaternionGenerators
