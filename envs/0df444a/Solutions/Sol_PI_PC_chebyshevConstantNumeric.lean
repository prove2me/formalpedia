-- Prove2me | solution 1 for PI.PC.chebyshevConstantNumeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:11:03.233823+00:00
-- url     : https://prove2.me/submissions/f6ee6668-2059-410c-b8bc-955c9fbae016

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PsiUpperBoundOfLtThirtyMulSixPow
import Theorems.Thm_PI_PC_log_thirty

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
theorem _root_.solution : ANum := by
  have h2 := log_two_gt_d9
  have h2' := log_two_lt_d9
  have h3 := log_three_gt_d9
  have h3' := log_three_lt_d9
  have h5 := log_five_gt_d9
  have h5' := log_five_lt_d9
  unfold ANum chA
  rw [log_thirty]
  constructor <;> norm_num at * <;> linarith
end PI.PC
