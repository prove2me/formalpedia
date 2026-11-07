-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:12.432936+00:00
-- url     : https://prove2.me/submissions/d67202ee-1820-4f82-bafd-91aabe95a42d

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Function.Injective (torusIndexMap f epsilon y hTwoF hOne hTwo) :=
  Subtype.val_injective.comp (torusIndexEquiv f epsilon y hTwoF hOne hTwo).injective
end QEC.Coding.ExpanderCodes.QuaternionGenerators
