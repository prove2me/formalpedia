-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:06.920139+00:00
-- url     : https://prove2.me/submissions/70d53129-0a62-4480-8e8c-77ec75d45ee2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic

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
theorem _root_.solution {x : K} {F : MvPowerSeries ι K} (hF : DivByMv x F) : DivByMv x (-F) := by
  intro d
  rw [map_neg, norm_neg]
  exact hF d
end ReciprocityTheory.ChartRestriction.L1
