-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_row3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:42:32.731753+00:00
-- url     : https://prove2.me/submissions/9bed8e23-400c-4acf-be1c-3f41333c93d7

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.r ⟨9+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 22 (RH132BernsteinImag134p4To135.a ⟨9+i.val, by omega⟩) j := by
  decide +kernel
