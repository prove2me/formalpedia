-- Prove2me | solution 1 for PI.SlopeSteps.natPowPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:29.024582+00:00
-- url     : https://prove2.me/submissions/e63e2c18-6295-4143-a366-003273847b6a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility
namespace PI.SlopeSteps
theorem _root_.solution (N k : ℕ) (hk : N = 0 → k = 0) : (0 : ℚ) < (N : ℚ) ^ k := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [hk h0, pow_zero]; exact one_pos
  · exact pow_pos (by exact_mod_cast h0) k
end PI.SlopeSteps
