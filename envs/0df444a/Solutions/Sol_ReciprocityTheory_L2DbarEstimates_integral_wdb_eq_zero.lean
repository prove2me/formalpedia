-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_wdb_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:57.15088+00:00
-- url     : https://prove2.me/submissions/a9f2b00a-f2b9-426d-8e82-4b7a21b0922b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_fderiv_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (j : Fin n) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) : ∫ y, wdb n j H y = 0 := by
  unfold wdb
  have i1 : Integrable (fun y => fderiv ℝ H y (bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => fderiv ℝ H y (Complex.I • bas n j)) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)
  rw [integral_div, integral_add i1 (i2.const_mul Complex.I), integral_const_mul,
    integral_fderiv_apply_eq_zero n H hH hc, integral_fderiv_apply_eq_zero n H hH hc]
  simp
end ReciprocityTheory.L2DbarEstimates
