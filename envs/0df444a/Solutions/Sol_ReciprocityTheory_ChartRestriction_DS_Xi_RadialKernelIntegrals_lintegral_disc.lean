-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:13.780993+00:00
-- url     : https://prove2.me/submissions/b66fff8d-63b7-4349-9b48-abc259b4a9f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_radial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RadialKernelIntegrals_lintegral_Ioc_rpow

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
theorem _root_.solution (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-a))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - a) / (2 - a))) := by
  have hm : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-a)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Iic ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-a))) r = (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r := by
    intro r hr
    by_cases h : r ∈ Iic ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, lintegral_Ioc_rpow a ρ ha hρ,
    ← ENNReal.ofReal_mul (by positivity)]
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
