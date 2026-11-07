-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedRight_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:56.021121+00:00
-- url     : https://prove2.me/submissions/36afdd52-dcd7-47f9-bf27-03f025d8b840

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_prime_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo) :=
  (constantTorus_conjugate_prime_injective f epsilon y hEpsilon hY hOne hTwo).comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective
end QEC.Coding.ExpanderCodes.QuaternionGenerators
