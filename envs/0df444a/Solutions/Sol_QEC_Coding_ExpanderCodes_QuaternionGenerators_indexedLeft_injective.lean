-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:22.238164+00:00
-- url     : https://prove2.me/submissions/7b892db9-8130-4fa6-b7a5-acae79f45e90

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_base_injective


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
    Function.Injective (indexedLeft f epsilon y hTwoF hY hOne hTwo) :=
  (constantTorus_conjugate_base_injective f epsilon y hEpsilon hY hOne hTwo).comp
    (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective
end QEC.Coding.ExpanderCodes.QuaternionGenerators
