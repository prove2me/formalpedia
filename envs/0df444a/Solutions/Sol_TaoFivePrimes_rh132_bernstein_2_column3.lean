-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_2_column3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:40:51.44587+00:00
-- url     : https://prove2.me/submissions/857ce956-66f4-45ac-bf58-665e45ddeae9

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.b ⟨9+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 11 (fun u => RH132BernsteinNegative133p8To134p4.r u j) ⟨9+i.val, by omega⟩ := by
  decide +kernel
