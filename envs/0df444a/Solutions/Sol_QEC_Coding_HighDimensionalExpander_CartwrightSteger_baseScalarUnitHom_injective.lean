-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseScalarUnitHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:49.137386+00:00
-- url     : https://prove2.me/submissions/99cea7fc-7da7-4970-bb28-2203687cf913

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Function.Injective (baseScalarUnitHom P r) :=
  Units.map_injective (algebraMap (BaseField P)
    (ConstantExtension P r)).injective
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
