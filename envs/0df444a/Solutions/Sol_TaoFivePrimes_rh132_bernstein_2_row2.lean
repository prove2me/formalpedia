-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_2_row2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:40:14.257281+00:00
-- url     : https://prove2.me/submissions/9a43a252-d47a-483a-b8fd-76bf89740479

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinNegative133p8To134p4.r ⟨6+i.val, by omega⟩ j = RH132BernsteinNegative133p8To134p4.transform 22 (RH132BernsteinNegative133p8To134p4.a ⟨6+i.val, by omega⟩) j := by
  decide +kernel
