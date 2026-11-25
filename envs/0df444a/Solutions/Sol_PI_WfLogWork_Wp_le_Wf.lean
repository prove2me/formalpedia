-- Prove2me | solution 1 for PI.WfLogWork.Wp_le_Wf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:31.798337+00:00
-- url     : https://prove2.me/submissions/ef4c15a3-c39b-4e4c-a73a-5269d44840ee

import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof
namespace PI.WfLogWork
theorem _root_.solution {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ Wp p) : x ∈ Wf p := by
  show PI.InWf x
  unfold PI.InWf
  exact ⟨0, by rw [pow_zero, one_mul]; exact h⟩
end PI.WfLogWork
