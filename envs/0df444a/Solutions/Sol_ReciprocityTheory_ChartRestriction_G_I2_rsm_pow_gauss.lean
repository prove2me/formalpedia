-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_pow_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:13:30.237334+00:00
-- url     : https://prove2.me/submissions/62fc9311-bbfb-4840-b20b-0e288983648b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ k * Real.exp (-y ^ 2) = (1 / 2) * Real.Gamma ((k + 1) / 2) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  first
    | (have h := integral_rpow_mul_exp_neg_rpow (two_pos : (0 : ℝ) < 2) hk
       simp only [Real.rpow_natCast, Real.rpow_two] at h
       exact h)
    | (have h := integral_rpow_mul_exp_neg_mul_rpow (two_pos : (0 : ℝ) < 2) hk one_pos
       simp only [Real.rpow_natCast, Real.rpow_two, neg_mul, one_mul, Real.one_rpow] at h
       rw [h]
       norm_num)
end ReciprocityTheory.ChartRestriction.G.I2
