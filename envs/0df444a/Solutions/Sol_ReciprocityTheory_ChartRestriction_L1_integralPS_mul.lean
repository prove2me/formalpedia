-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:30.140329+00:00
-- url     : https://prove2.me/submissions/55a1ce56-c062-4c40-aea2-465b2c61545b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_mul

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
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g) :
    IntegralPS (f * g) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_mul hf hg
end ReciprocityTheory.ChartRestriction.L1
