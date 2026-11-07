-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_eq_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:41.913902+00:00
-- url     : https://prove2.me/submissions/23b5af7a-4a20-4ebb-a76a-e7ed98f6ffcc

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceOnePlusY_eq_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    sourceYPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank - 1 := by
  rw [sourceYPolynomial, sourceOnePlusY_eq_pow]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
