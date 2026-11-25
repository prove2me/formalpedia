-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals.lintegral_Ioi_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:15.103421+00:00
-- url     : https://prove2.me/submissions/6ee8ab70-8b40-4aa7-8bb1-ffac4278c274

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
theorem _root_.solution (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ (1 - b)) = ENNReal.ofReal (ρ ^ (2 - b) / (b - 2)) := by
  have hr : 1 - b < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hρ)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => Real.rpow_nonneg (hρ.trans hr).le _)),
    integral_Ioi_rpow_of_lt hr hρ]
  congr 1
  rw [show 1 - b + 1 = 2 - b by ring, show b - 2 = -(2 - b) by ring, div_neg, neg_div]
end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals
