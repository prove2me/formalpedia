-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:01.611942+00:00
-- url     : https://prove2.me/submissions/9799b054-f11e-4014-a4b4-73dec7a135ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divByMv_add

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
theorem _root_.solution {x : K} {α : Type} (s : Finset α) (F : α → MvPowerSeries ι K)
    (hF : ∀ i ∈ s, DivByMv x (F i)) : DivByMv x (∑ i ∈ s, F i) := by
  exact Finset.sum_induction _ (DivByMv x) (fun _ _ => divByMv_add) (divByMv_zero x) hF
end ReciprocityTheory.ChartRestriction.L1
