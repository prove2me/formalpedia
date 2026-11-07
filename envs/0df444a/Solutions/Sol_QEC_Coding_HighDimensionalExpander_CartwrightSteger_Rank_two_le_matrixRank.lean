-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.two_le_matrixRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:37:44.760321+00:00
-- url     : https://prove2.me/submissions/d18d11f4-596d-490b-8177-418a9bb0dee6

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
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
theorem _root_.solution (r : Rank) : 2 <= r.matrixRank := by
  cases r <;> simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
