-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantRegularMatrix_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:06.363778+00:00
-- url     : https://prove2.me/submissions/d74f7da6-5444-4c90-a86b-8b95985227e2

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Function.Injective (constantRegularMatrix P r) :=
  Algebra.leftMulMatrix_injective (constantBasis P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
