-- Prove2me | solution 1 for P2M_PI_SqfRootShift_W_aeval_eq_zero_of_dvd__aabcf90c1878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:48.806669+00:00
-- url     : https://prove2.me/submissions/f56beab7-9ced-497c-b5de-005e2b2b0dc6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootShift.W
theorem _root_.solution {P Q : (ZMod g)[X]} (h : P ∣ Q) {z : Fbar g}
    (hz : aeval z P = 0) : aeval z Q = 0 := by
  obtain ⟨q, rfl⟩ := h
  simp [hz]
end PI.SqfRootShift.W
