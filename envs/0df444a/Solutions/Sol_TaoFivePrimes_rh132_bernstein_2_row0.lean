-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_2_row0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:39:52.577799+00:00
-- url     : https://prove2.me/submissions/4954ef0e-11da-4342-bd66-16646642c2fd

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.r ⟨0+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 22 (RH132BernsteinNegative133p8To134p4.a ⟨0+i.val, by omega⟩) j := by
  decide +kernel
