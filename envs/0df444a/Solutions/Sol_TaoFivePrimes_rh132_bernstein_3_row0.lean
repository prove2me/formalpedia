-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_row0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:41:50.682447+00:00
-- url     : https://prove2.me/submissions/765a25e8-0b47-4705-a8a0-7c8171a942d3

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.r ⟨0+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 22 (RH132BernsteinImag134p4To135.a ⟨0+i.val, by omega⟩) j := by
  decide +kernel
