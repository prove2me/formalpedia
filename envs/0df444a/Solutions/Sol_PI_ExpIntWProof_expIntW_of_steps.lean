-- Prove2me | solution 1 for PI.ExpIntWProof.expIntW_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:09.536529+00:00
-- url     : https://prove2.me/submissions/de98221d-bb29-4797-a722-ed8483045948

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (h1 : StepI) (h3 : StepIII) : ExpIntW := by
  intro p _ σ f hf hs
  obtain ⟨h0, hint⟩ := hs
  rw [sub_zero] at h0 hint
  refine ⟨by rw [sub_zero]; exact h0, ?_⟩
  rw [sub_zero]
  intro n
  exact h3 p _ (h1 p σ f hf n) (hint n)
end PI.ExpIntWProof
