-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_8_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:15:59.880929+00:00
-- url     : https://prove2.me/submissions/2dcd0947-3739-4002-9be6-269f4a4ac6c8

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 8 (0+m.val),
      RHDirect132Integer.gammaIm 8 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 0 []).getD (0+m.val) (0,0)) := by
  decide +kernel
