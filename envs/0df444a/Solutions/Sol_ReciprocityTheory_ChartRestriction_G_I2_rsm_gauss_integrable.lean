-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_gauss_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:13:19.542268+00:00
-- url     : https://prove2.me/submissions/9ad1ec64-965c-4adc-b1c1-7b69db4083ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_gauss_total

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
theorem _root_.solution (N : ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin N) => Real.exp (-‖z‖ ^ 2)) := by
  first
    | exact Integrable.of_integral_ne_zero (by rw [rsm_gauss_total]; positivity)
    | (have h := GaussianFourier.integrable_rexp_neg_mul_sq_norm (V := EuclideanSpace ℂ (Fin N)) one_pos
       simp only [neg_mul, one_mul] at h
       exact h)
end ReciprocityTheory.ChartRestriction.G.I2
