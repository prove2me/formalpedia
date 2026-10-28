-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_2_row3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:40:22.614724+00:00
-- url     : https://prove2.me/submissions/51712637-178d-4be9-891e-7706a748fe7d

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.r ⟨9+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 22 (RH132BernsteinNegative133p8To134p4.a ⟨9+i.val, by omega⟩) j := by
  decide +kernel
