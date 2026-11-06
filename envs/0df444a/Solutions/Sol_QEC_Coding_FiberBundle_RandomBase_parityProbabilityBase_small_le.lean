-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.parityProbabilityBase_small_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:31:08.842043+00:00
-- url     : https://prove2.me/submissions/1b24dc7d-9cd6-4f31-93b7-58fce1ec72d2

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_parityProbabilityBase_le_expEnvelope

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (p : Real) (w : Nat) (hp0 : 0 ≤ p) (hpHalf : p ≤ 1 / 2)
    (hsmall : p * w ≤ 1) :
    (1 + (1 - 2 * p) ^ w) / 2 ≤
      Real.exp (-(p * w) / 2) := by
  let x : Real := p * w
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := hsmall
  calc
    _ ≤ (1 + Real.exp (-2 * x)) / 2 :=
      parityProbabilityBase_le_expEnvelope p w hpHalf
    _ = Real.exp (-x) * Real.cosh x := by
      rw [Real.cosh_eq]
      rw [show -2 * x = -(x + x) by ring, Real.exp_neg, Real.exp_add,
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ ≤ Real.exp (-x) * Real.exp (x ^ 2 / 2) := by
      gcongr
      exact Real.cosh_le_exp_half_sq x
    _ = Real.exp (-x + x ^ 2 / 2) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-x / 2) := by
      apply Real.exp_le_exp_of_le
      nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx1)]
end QEC.Coding.FiberBundle.RandomBase
