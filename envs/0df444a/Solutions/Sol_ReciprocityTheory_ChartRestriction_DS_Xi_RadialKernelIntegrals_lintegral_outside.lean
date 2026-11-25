-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_outside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:16.794115+00:00
-- url     : https://prove2.me/submissions/2172db46-7298-4868-bf3a-b3d6909b804b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_radial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_Ioi_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
theorem _root_.solution (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-b))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - b) / (b - 2))) := by
  have hm : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-b)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Ioi ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-b))) r = (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - b))) r := by
    intro r hr
    by_cases h : r ∈ Ioi ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hρ.le,
    lintegral_Ioi_rpow b ρ hb hρ, ← ENNReal.ofReal_mul (by positivity)]
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
