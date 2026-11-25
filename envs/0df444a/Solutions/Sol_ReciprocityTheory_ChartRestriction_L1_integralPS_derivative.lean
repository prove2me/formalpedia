-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.integralPS_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:01.511299+00:00
-- url     : https://prove2.me/submissions/6b4ab1cc-37b8-44e6-b940-e403ad0de6a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_integralPS_iff_divBy_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_derivative

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
theorem _root_.solution {f : PowerSeries K} (hf : IntegralPS f) :
    IntegralPS (derivative K f) := by
  rw [integralPS_iff_divBy_one] at *
  exact divBy_derivative hf
end ReciprocityTheory.ChartRestriction.L1
