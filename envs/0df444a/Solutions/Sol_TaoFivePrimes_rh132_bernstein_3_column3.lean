-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_column3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:43:04.98298+00:00
-- url     : https://prove2.me/submissions/02c03f5e-5687-4d92-b55e-75a08cf6a2f8

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag134p4To135.b ⟨9+i.val, by omega⟩ j = RH132BernsteinImag134p4To135.transform 11 (fun u => RH132BernsteinImag134p4To135.r u j) ⟨9+i.val, by omega⟩ := by
  decide +kernel
