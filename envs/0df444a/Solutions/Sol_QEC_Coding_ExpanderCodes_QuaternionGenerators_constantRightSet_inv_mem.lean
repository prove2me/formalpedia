-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantRightSet_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:02.267456+00:00
-- url     : https://prove2.me/submissions/7aebb713-6a6a-4839-98cd-edcfdec134fe

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_inv_mem_conjugacySet_of_sq_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    {g : ProjectiveGroup (f epsilon) y}
    (hg : g ∈ constantRightSet f epsilon y hEpsilon hY hOne) :
    g⁻¹ ∈ constantRightSet f epsilon y hEpsilon hY hOne :=
  inv_mem_conjugacySet_of_sq_one _ _
    (projectivePrime_sq (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne) hg
end QEC.Coding.ExpanderCodes.QuaternionGenerators
