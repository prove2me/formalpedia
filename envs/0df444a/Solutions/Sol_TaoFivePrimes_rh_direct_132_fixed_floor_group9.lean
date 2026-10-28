-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fixed_floor_group9
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:49:51.839605+00:00
-- url     : https://prove2.me/submissions/deef63cb-e765-44dd-8a5c-75797a2aab2f

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ j : Fin 5,
    RHDirect132FastNumerator.floorHolds (45+j.val) := by
  unfold RHDirect132FastNumerator.floorHolds
  decide +kernel
