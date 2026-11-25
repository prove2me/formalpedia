-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.mul_le_sqrt_mul_sqrt_mul_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:56.652001+00:00
-- url     : https://prove2.me/submissions/a18068db-cd58-4306-a86b-c5f15d7c4cc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {u v A B P Q t : ℝ} (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t) (huP : u ^ 2 ≤ A * P) (hvQ : v ^ 2 ≤ B * Q) :
    u * v ≤ Real.sqrt A * Real.sqrt B * ((t * P + Q / t) / 2) := by
  have hu : |u| ≤ Real.sqrt A * Real.sqrt P := by
    rw [← Real.sqrt_mul hA, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt huP
  have hv' : v ≤ Real.sqrt B * Real.sqrt Q := by
    rw [← Real.sqrt_mul hB, ← Real.sqrt_sq hv]
    exact Real.sqrt_le_sqrt hvQ
  have hPQ : Real.sqrt P * Real.sqrt Q ≤ (t * P + Q / t) / 2 := by
    have key : 2 * t * (Real.sqrt P * Real.sqrt Q) ≤ t ^ 2 * P + Q := by
      nlinarith [sq_nonneg (t * Real.sqrt P - Real.sqrt Q), Real.sq_sqrt hP, Real.sq_sqrt hQ]
    have e : (t * P + Q / t) / 2 = (t ^ 2 * P + Q) / (2 * t) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  calc u * v ≤ |u| * v := mul_le_mul_of_nonneg_right (le_abs_self u) hv
    _ ≤ (Real.sqrt A * Real.sqrt P) * (Real.sqrt B * Real.sqrt Q) :=
        mul_le_mul hu hv' hv (by positivity)
    _ = Real.sqrt A * Real.sqrt B * (Real.sqrt P * Real.sqrt Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hPQ (by positivity)
end ReciprocityTheory.ChartRestriction.G.I2
