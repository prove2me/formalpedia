-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:15.128937+00:00
-- url     : https://prove2.me/submissions/d2fc71d4-78e4-49a5-b3dd-8aa20e1ff695

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_pow

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
theorem _root_.solution {f : PowerSeries K} (hf : IntegralPS f) (n : ℕ) : IntegralPS (f ^ n) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_pow hf n
end ReciprocityTheory.ChartRestriction.L1
