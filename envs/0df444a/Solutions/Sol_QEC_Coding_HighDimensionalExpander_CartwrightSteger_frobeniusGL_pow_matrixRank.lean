-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_pow_matrixRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:59.508172+00:00
-- url     : https://prove2.me/submissions/e7bfa77c-edb3-4990-890c-8195af5ec622

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_matrixRank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    frobeniusGL P r ^ r.matrixRank = 1 := by
  apply (Matrix.GeneralLinearGroup.toLin' (constantBasis P r)).injective
  rw [map_pow, map_one]
  simp only [frobeniusGL, MulEquiv.apply_symm_apply]
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
    (BaseField P) (ConstantExtension P r)).injective
  rw [map_pow, map_one]
  change (constantFrobenius P r).toLinearEquiv ^ r.matrixRank = 1
  have hpow : ∀ n : Nat,
      (constantFrobenius P r).toLinearEquiv ^ n =
        (constantFrobenius P r ^ n).toLinearEquiv := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, pow_succ, ih]
        rfl
  rw [hpow, constantFrobenius_pow_matrixRank]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
