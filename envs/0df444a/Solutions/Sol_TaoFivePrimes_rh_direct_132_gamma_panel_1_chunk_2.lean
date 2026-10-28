-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_1_chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:12:34.649089+00:00
-- url     : https://prove2.me/submissions/fcf8c6c4-d9a6-4a07-95db-6e764a02021c

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 1 (40+m.val),
      RHDirect132Integer.gammaIm 1 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 1 []).getD (40+m.val) (0,0)) := by
  decide +kernel
