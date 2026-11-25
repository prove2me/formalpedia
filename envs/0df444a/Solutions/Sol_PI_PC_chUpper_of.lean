-- Prove2me | solution 1 for PI.PC.chUpper_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:11.020812+00:00
-- url     : https://prove2.me/submissions/3aa5675c-c8bd-4296-b46a-efb91f066d80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Theorems.Thm_PI_PC_psiUpperBound_of_lt_thirty_mul_six_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PC
open Real
namespace PI.PC
theorem _root_.solution (hA : ANum) (hD : DUpper) (hS : Sandwich) : CHUpper := by
  intro x h1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 6)
  refine psiUpperBound_of_lt_thirty_mul_six_pow hA hD hS k x h1 ?_
  have : (0 : ℝ) < 6 ^ k := by positivity
  linarith
end PI.PC
