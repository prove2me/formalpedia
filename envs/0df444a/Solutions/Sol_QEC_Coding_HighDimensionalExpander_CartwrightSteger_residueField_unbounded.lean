-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueField_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:52.804624+00:00
-- url     : https://prove2.me/submissions/de10a056-6f14-442b-b4b4-90785d5faa37

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BasePrime_two_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_BasePrime_one_le
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_residueField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) (bound : Nat) :
    ∃ level, bound < Nat.card (ResidueField P r level) := by
  refine ⟨bound, ?_⟩
  rw [natCard_residueField]
  calc
    bound < 2 ^ bound := bound.lt_two_pow_self
    _ <= P.q ^ bound := pow_le_pow_left' P.two_le bound
    _ <= P.q ^ (3 + bound) :=
      pow_le_pow_right' P.one_le (by omega)
    _ <= P.q ^ r.residueExponent bound := by
      apply pow_le_pow_right' P.one_le
      simp [Rank.residueExponent]
      have := Rank.two_le_matrixRank r
      omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
