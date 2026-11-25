-- Prove2me | solution 1 for PI.SqfRootShift.W.divByMonic_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:14.490257+00:00
-- url     : https://prove2.me/submissions/5b638fb5-f1a8-49b4-a1e3-52bdc2f5df7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC

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
theorem _root_.solution {r : ℕ} {f P : (ZMod g)[X]} (hf : IsLab g r f) (hP : P.Monic)
    (hdvd : P ∣ f) :
    f = P * (f /ₘ P) ∧ (f /ₘ P).Monic ∧ (f /ₘ P).natDegree = r - P.natDegree := by
  have hmod : f %ₘ P = 0 := (modByMonic_eq_zero_iff_dvd hP).2 hdvd
  have heq : f = P * (f /ₘ P) := by
    have := modByMonic_add_div f P
    rw [hmod, zero_add] at this
    exact this.symm
  refine ⟨heq, ?_, ?_⟩
  · apply hP.of_mul_monic_left
    rw [← heq]; exact hf.1
  · rw [natDegree_divByMonic f hP, hf.2.1]
end PI.SqfRootShift.W
