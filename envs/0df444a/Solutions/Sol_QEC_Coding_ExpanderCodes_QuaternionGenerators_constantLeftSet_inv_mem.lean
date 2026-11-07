-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantLeftSet_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:01.166396+00:00
-- url     : https://prove2.me/submissions/d55f7c07-be9f-474d-b2d2-645016a43205

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_mem_constantTorus
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_conjugate_base


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y} (hg : g ∈ constantLeftSet f epsilon y hY hOne) :
    g⁻¹ ∈ constantLeftSet f epsilon y hY hOne :=
  inv_mem_conjugacySet _ _ _ (projectiveAlpha_mem_constantTorus f epsilon y hEpsilon)
    (projectiveAlpha_conjugate_base (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) hg
end QEC.Coding.ExpanderCodes.QuaternionGenerators
