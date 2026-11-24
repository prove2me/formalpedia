-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:46:13.398873+00:00
-- url     : https://prove2.me/submissions/bb7df898-a86c-4abe-b1cb-bab9b0a3fc92

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
theorem _root_.solution {x : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv x G) :
    DivByMv x (F + G) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))
end ReciprocityTheory.ChartRestriction.L1
