-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_1_row1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:09:59.765226+00:00
-- url     : https://prove2.me/submissions/91d2219c-5e46-4e0f-91c1-bc7be49ffd30

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.r ⟨3+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 22 (RH132BernsteinImag133p2To133p8.a ⟨3+i.val, by omega⟩) j := by
  decide +kernel
