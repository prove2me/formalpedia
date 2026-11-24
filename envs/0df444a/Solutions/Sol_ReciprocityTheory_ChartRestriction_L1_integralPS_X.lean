-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:33.103864+00:00
-- url     : https://prove2.me/submissions/dcba219e-e806-45d0-8bd2-e4b3707798d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_X
import Theorems.Thm_Formalism_LT_Asm_integralMv_X


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
theorem _root_.solution : IntegralPS (X : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr (integralMv_X ())
end ReciprocityTheory.ChartRestriction.L1
