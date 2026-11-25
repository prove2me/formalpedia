-- Prove2me | solution 1 for PI.VacEntire.UnitaryGroupMassFormula.tensEntire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:16.400796+00:00
-- url     : https://prove2.me/submissions/8c6705cd-0b5c-4de9-8ccb-2d092052a754

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft

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
theorem _root_.solution : TensEntire := by
  intro n _ θ N N' hθ c _
  unfold tensPow
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_prod _ (fun j _ => ?_)
  have he : (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) = ⇑(blockL n N N' i j) := by
    funext z τ
    rfl
  have hb : AnalyticAt ℂ (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) c := by
    rw [he]
    exact (blockL n N N' i j).analyticAt c
  exact (hθ _ (Set.mem_univ _)).comp hb
end PI.VacEntire.UnitaryGroupMassFormula
