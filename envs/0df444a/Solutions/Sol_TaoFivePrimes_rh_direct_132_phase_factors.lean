-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_phase_factors
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:00:29.542393+00:00
-- url     : https://prove2.me/submissions/5e8be745-4ecf-4aa7-9037-12201b9bf33a

import Definitions.Def_TaoFivePrimes_RHDirect132PhaseFactors
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

theorem solution : ∀ l : Fin 184,
    TaoFivePrimes_RHDirect132PhaseFactors.getD l.val 0 =
      99^l.val * 8^(183-l.val) * ((183:ℕ).factorial/(l.val.factorial)) := by
  decide +kernel
