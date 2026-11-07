-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank.source_size_condition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:28.224657+00:00
-- url     : https://prove2.me/submissions/24adaa30-54a9-419a-88c7-e69904eda03f

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BasePrime_one_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
theorem _root_.solution (P : BasePrime) (r : Rank) (level : Nat) :
    4 * r.matrixRank ^ 2 <= P.q ^ r.residueExponent level := by
  calc
    4 * r.matrixRank ^ 2 <= 64 := by cases r <;> norm_num [matrixRank]
    _ <= 5 ^ 3 := by norm_num
    _ <= P.q ^ 3 := pow_le_pow_left' P.five_le 3
    _ <= P.q ^ (3 + level) :=
      pow_le_pow_right' P.one_le (by omega)
    _ <= P.q ^ r.residueExponent level := by
      apply pow_le_pow_right' P.one_le
      simp [residueExponent]
      have := two_le_matrixRank r
      omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.Rank
