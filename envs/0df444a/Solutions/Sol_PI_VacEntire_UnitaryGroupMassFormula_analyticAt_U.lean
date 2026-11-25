-- Prove2me | solution 1 for PI.VacEntire.UnitaryGroupMassFormula.analyticAt_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:58.631872+00:00
-- url     : https://prove2.me/submissions/0acee0e1-db42-4a48-89ca-92b881b89c3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
import Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_Hf_left

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
    (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (U A x G) c := by
  unfold U
  refine AnalyticAt.mul ?_ ?_
  · have hshift : AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z + x) c :=
      analyticAt_id.add analyticAt_const
    exact (hG (c + x) (Set.mem_univ _)).comp (f := fun z => z + x) hshift
  · refine AnalyticAt.cexp' ?_
    exact (analyticAt_const.mul (analyticAt_Hf_left A x c)).sub analyticAt_const
end PI.VacEntire.UnitaryGroupMassFormula
