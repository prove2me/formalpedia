-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantSets_total_nonconjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:03.542216+00:00
-- url     : https://prove2.me/submissions/4828e039-72d9-4a38-bd32-fdb8d2c83161

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugacySet_total_nonconjugacy
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveBase_sq_ne_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) {a b : ProjectiveGroup (f epsilon) y}
    (ha : a ∈ constantLeftSet f epsilon y hY hOne)
    (hb : b ∈ constantRightSet f epsilon y hEpsilon hY hOne)
    (g : ProjectiveGroup (f epsilon) y) : a * g ≠ g * b :=
  conjugacySet_total_nonconjugacy _ _ _ _
    (projectiveBase_sq_ne_one (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne hTwo)
    (projectivePrime_sq (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) ha hb g
end QEC.Coding.ExpanderCodes.QuaternionGenerators
