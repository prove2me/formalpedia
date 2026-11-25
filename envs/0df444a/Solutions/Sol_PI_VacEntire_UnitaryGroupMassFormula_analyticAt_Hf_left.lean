-- Prove2me | solution 1 for PI.VacEntire.UnitaryGroupMassFormula.analyticAt_Hf_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:04.972534+00:00
-- url     : https://prove2.me/submissions/bfbdc259-36f8-42ca-8720-344d73f13e69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
import Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VacEntire PI.VacEntire.UnitaryGroupMassFormula
open PI.VacEntire
namespace PI.VacEntire.UnitaryGroupMassFormula
theorem _root_.solution {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z => Hf A z x) c := by
  unfold Hf
  refine AnalyticAt.div_const ?_
  refine Finset.analyticAt_fun_sum _ (fun τ _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
  exact (analyticAt_coord τ i j c).mul analyticAt_const
end PI.VacEntire.UnitaryGroupMassFormula
