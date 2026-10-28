-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_1_row3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:10:34.91625+00:00
-- url     : https://prove2.me/submissions/3dc3c0e6-581c-4432-8ac5-8d4091486cc1

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.r ⟨9+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 22 (RH132BernsteinImag133p2To133p8.a ⟨9+i.val, by omega⟩) j := by
  decide +kernel
