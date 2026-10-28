-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_column1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:42:45.859258+00:00
-- url     : https://prove2.me/submissions/17634086-3895-4af5-8667-91116c5d8dc5

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.b ⟨3+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 11 (fun u => RH132BernsteinImag134p4To135.r u j) ⟨3+i.val, by omega⟩ := by
  decide +kernel
