-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:05.068261+00:00
-- url     : https://prove2.me/submissions/d6837625-c217-4023-937b-c4bb825c57d3

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
    (hTwoF : (2 : F) ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (QuotientGroup.mk a) =
      constantProjectiveMap f epsilon y a := rfl
end QEC.Coding.ExpanderCodes.QuaternionGenerators
