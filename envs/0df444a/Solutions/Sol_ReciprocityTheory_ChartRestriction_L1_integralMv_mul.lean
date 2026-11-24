-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralMv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:04.926811+00:00
-- url     : https://prove2.me/submissions/cbefd820-c125-40f4-9ecd-ebef4249f969

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_mul

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
variable {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  rw [integralMv_iff_divBy_one] at *
  have h := divByMv_mul hF hG
  rwa [one_mul] at h
end ReciprocityTheory.ChartRestriction.L1
