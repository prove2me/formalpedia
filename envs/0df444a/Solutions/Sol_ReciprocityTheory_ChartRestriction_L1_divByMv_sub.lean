-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:13.206035+00:00
-- url     : https://prove2.me/submissions/5df4eb73-d564-49fe-8ef5-3c7042072840

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
    DivByMv x (F - G) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hF d) (by rw [norm_neg]; exact hG d))
end ReciprocityTheory.ChartRestriction.L1
