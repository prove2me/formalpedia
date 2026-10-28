-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_11_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:17:29.064118+00:00
-- url     : https://prove2.me/submissions/f9c7de25-12a0-45a8-bd8f-a4c6068a38c8

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 11 (0+m.val),
      RHDirect132Integer.gammaIm 11 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 3 []).getD (0+m.val) (0,0)) := by
  decide +kernel
