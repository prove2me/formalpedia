-- Prove2me | solution 1 for PI.WeylForKInhab.triv_urep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:50.320322+00:00
-- url     : https://prove2.me/submissions/9455e5a7-fc4f-41ea-84f4-9523d75e8fe0

import Definitions.Def_Formalism_PeriodIntegrals_WeylForK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UpqRep Matrix
noncomputable section
open PI PI.WeylForKInhab
namespace PI.WeylForKInhab
theorem _root_.solution {N : ℕ} (ε : Fin N → Bool) : IsURepOn (Kset ε) (triv N) := by
  refine ⟨⟨rfl, fun a _ b _ => rfl⟩, fun g _ v => rfl, fun v => ?_⟩
  show ContinuousOn (fun _ => (1 : ℂ →L[ℂ] ℂ) v) _
  exact continuousOn_const
end PI.WeylForKInhab
