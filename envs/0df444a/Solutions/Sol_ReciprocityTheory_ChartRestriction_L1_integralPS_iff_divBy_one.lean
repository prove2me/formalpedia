-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_iff_divBy_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:23.237869+00:00
-- url     : https://prove2.me/submissions/0d0359e3-6191-49b6-9f38-51ec510163d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralMv_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_mv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_iff_mv

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
theorem _root_.solution (f : PowerSeries K) : IntegralPS f ↔ DivBy (1 : K) f := by
  rw [integralPS_iff_mv, integralMv_iff_divBy_one, divBy_iff_mv]
end ReciprocityTheory.ChartRestriction.L1
