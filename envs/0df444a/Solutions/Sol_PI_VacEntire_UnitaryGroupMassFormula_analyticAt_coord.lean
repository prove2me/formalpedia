-- Prove2me | solution 1 for PI.VacEntire.UnitaryGroupMassFormula.analyticAt_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:13.989992+00:00
-- url     : https://prove2.me/submissions/9ed137dc-bb66-4772-ba6a-2d8536083063

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
theorem _root_.solution {ι : Type} [Fintype ι] {N N' : ℕ} (τ : ι) (i : Fin N') (j : Fin N)
    (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z τ i j) c :=
  (coordL ι N N' τ i j).analyticAt c
end PI.VacEntire.UnitaryGroupMassFormula
