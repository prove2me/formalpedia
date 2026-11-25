-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cut_rho_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:08:37.289558+00:00
-- url     : https://prove2.me/submissions/ff066ff0-6ec3-4f03-8973-c9269ef398cf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutL_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cut_rho_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    s⁻¹ ≤ 4 * (s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s) := by
  have hs0 : 0 < s := lt_of_lt_of_le hε hs
  have hL := cutL_nonneg hε hs0.le
  rw [cut_rho_eq (by linarith), inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hs0 (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 3 * s + ε),
    mul_nonneg hs0.le (mul_nonneg hε.le hL)]
end ReciprocityTheory.L2DbarEstimates.C
