-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_row1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:42:15.551874+00:00
-- url     : https://prove2.me/submissions/7aad0412-a334-4fc7-a0b4-f1b2234aafeb

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.r ⟨3+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 22 (RH132BernsteinImag134p4To135.a ⟨3+i.val, by omega⟩) j := by
  decide +kernel
