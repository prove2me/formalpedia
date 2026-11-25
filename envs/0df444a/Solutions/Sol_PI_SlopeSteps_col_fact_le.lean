-- Prove2me | solution 1 for PI.SlopeSteps.col_fact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:57.432411+00:00
-- url     : https://prove2.me/submissions/fd27fb7f-5d75-46c1-b7de-e85cf34dbfc5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Theorems.Thm_PI_SlopeSteps_multinomial_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.SlopeSteps
open Finset
namespace PI.SlopeSteps
theorem _root_.solution {N : ℕ} (f : Fin N → ℕ) :
    (∑ a, f a).factorial ≤ N ^ (∑ a, f a) * ∏ a, (f a).factorial := by
  rw [← Nat.multinomial_spec univ f, mul_comm]
  exact Nat.mul_le_mul_right _ (multinomial_le_pow f)
end PI.SlopeSteps
