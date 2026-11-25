-- Prove2me | solution 1 for PI.SqfRootsInj.W.two_mul_le_of_dvd_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:22.590051+00:00
-- url     : https://prove2.me/submissions/fcfb9b0b-3aca-4e65-89b8-c8f1591049de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain

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
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootsInj.W
theorem _root_.solution {J E : ℕ} (hd : J ∣ E) (hne : J ≠ E) (hE : 1 ≤ E) : 2 * J ≤ E := by
  obtain ⟨c, hc⟩ := hd
  subst hc
  rcases Nat.lt_or_ge c 2 with h | h
  · interval_cases c
    · omega
    · exact absurd (mul_one J).symm hne
  · nlinarith
end PI.SqfRootsInj.W
