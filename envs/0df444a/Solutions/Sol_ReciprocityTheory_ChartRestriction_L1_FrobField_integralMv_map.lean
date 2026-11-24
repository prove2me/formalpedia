-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.FrobField.integralMv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:52.992393+00:00
-- url     : https://prove2.me/submissions/a9d6896a-b328-450a-9dd5-61673f829124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
variable {l : ℕ} {σ : K →+* K} {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
namespace FrobField
theorem _root_.solution (h : FrobField K l σ) {F : MvPowerSeries ι K} (hF : IntegralMv F) :
    IntegralMv (MvPowerSeries.map σ F) := by
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_map, h.isom]
  exact (integralMv_iff_divBy_one F).mp hF d
end FrobField
end ReciprocityTheory.ChartRestriction.L1
