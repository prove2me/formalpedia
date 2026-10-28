-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fixed_floor_group11
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:50:09.868808+00:00
-- url     : https://prove2.me/submissions/b6ded083-8620-4178-9376-941c82e48b24

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ j : Fin 5,
    RHDirect132FastNumerator.floorHolds (55+j.val) := by
  unfold RHDirect132FastNumerator.floorHolds
  decide +kernel
