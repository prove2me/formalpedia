-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceYPolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:27.577195+00:00
-- url     : https://prove2.me/submissions/6ecac102-2ddd-4bb0-93bc-1848eb794d24

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceYPolynomial_eq_pow_sub_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    (sourceYPolynomial P r).natDegree = r.matrixRank := by
  rw [sourceYPolynomial_eq_pow_sub_one]
  have hmonic :
      (1 + Polynomial.X : PolynomialRing P).Monic := by
    simpa [add_comm] using
      (Polynomial.monic_X_add_C (1 : BaseField P))
  have hpowDegree :
      ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank).natDegree =
        r.matrixRank := by
    rw [hmonic.natDegree_pow]
    have hbase :
        (1 + Polynomial.X : PolynomialRing P).natDegree = 1 := by
      simpa [add_comm] using
        (Polynomial.natDegree_X_add_C (1 : BaseField P))
    rw [hbase, Nat.mul_one]
  calc
    ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank - 1).natDegree =
        ((1 + Polynomial.X : PolynomialRing P) ^ r.matrixRank).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [Polynomial.natDegree_one, hpowDegree]
      exact lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
    _ = r.matrixRank := hpowDegree
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
