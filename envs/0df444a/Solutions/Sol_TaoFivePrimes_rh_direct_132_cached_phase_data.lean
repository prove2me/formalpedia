-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_cached_phase_data
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:28:35.19972+00:00
-- url     : https://prove2.me/submissions/7a1b5137-2f21-472a-934c-0f78f562589c

import Definitions.Def_TaoFivePrimes_RHDirect132CachedRule
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

theorem solution : ∀ i : Fin 16,
    RHDirect132CachedRule.phaseData.getD i.val (0,0) =
      RHDirectPhase132.panels i.val := by
  decide +kernel
