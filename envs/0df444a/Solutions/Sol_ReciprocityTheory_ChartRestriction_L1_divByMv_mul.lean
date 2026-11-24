-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divByMv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:12.472813+00:00
-- url     : https://prove2.me/submissions/490c23c2-f509-47b7-8ee3-160507294f2f

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
theorem _root_.solution {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, norm_mul]
  refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ ‖x‖ * ‖y‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by rw [norm_zero]; positivity) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.L1
