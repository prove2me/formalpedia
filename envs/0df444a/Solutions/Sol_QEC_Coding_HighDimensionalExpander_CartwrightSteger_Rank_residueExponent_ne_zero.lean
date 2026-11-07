-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.residueExponent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:43:53.215639+00:00
-- url     : https://prove2.me/submissions/94c086e5-0641-4f89-a799-947f83d1598c

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
theorem _root_.solution (r : Rank) (level : Nat) :
    Not (r.residueExponent level = 0) := by
  cases r <;> simp [residueExponent, matrixRank]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
