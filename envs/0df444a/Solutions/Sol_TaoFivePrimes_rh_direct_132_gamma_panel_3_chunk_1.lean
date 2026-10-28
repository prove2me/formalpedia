-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_3_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:13:24.968419+00:00
-- url     : https://prove2.me/submissions/a1fafe30-365f-4c2c-911e-8a5db7b5e8aa

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 3 (20+m.val),
      RHDirect132Integer.gammaIm 3 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 3 []).getD (20+m.val) (0,0)) := by
  decide +kernel
