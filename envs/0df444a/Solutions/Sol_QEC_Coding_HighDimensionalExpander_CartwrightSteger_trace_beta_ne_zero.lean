-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.trace_beta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:29.953197+00:00
-- url     : https://prove2.me/submissions/33cd5cdd-e170-47fc-bfb8-11ec827a2170

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Not (Algebra.trace (BaseField P) (ConstantExtension P r) (beta P r) = 0) := by
  rw [beta, ← map_one (algebraMap (BaseField P) (ConstantExtension P r)),
    Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one]
  rw [GaloisField.finrank P.q (by cases r <;> simp [Rank.matrixRank])]
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt
    (lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r))
    (lt_of_le_of_lt (by cases r <;> simp [Rank.matrixRank]) P.five_le)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
