-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioc_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:12.78748+00:00
-- url     : https://prove2.me/submissions/064cc728-e7a0-45a1-bad9-f27066979871

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PlanarKernelBound

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
    ∫⁻ r in Ioc (0 : ℝ) ρ, ENNReal.ofReal (r ^ (1 - a)) = ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have hr : -1 < 1 - a := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegral.intervalIntegrable_rpow' hr).1)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => Real.rpow_nonneg hr.1.le _)),
    ← intervalIntegral.integral_of_le hρ.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith)]
  congr 1
  rw [show 1 - a + 1 = 2 - a by ring, sub_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
