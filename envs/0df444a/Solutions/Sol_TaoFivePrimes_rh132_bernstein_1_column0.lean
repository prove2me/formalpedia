-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_1_column0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:10:46.611534+00:00
-- url     : https://prove2.me/submissions/08df3dcf-004b-4ded-939d-cea8d7c85b4d

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.b ⟨0+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 11 (fun u => RH132BernsteinImag133p2To133p8.r u j) ⟨0+i.val, by omega⟩ := by
  decide +kernel
