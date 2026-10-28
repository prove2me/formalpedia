-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_10_chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:17:18.636404+00:00
-- url     : https://prove2.me/submissions/2bd8487c-b930-42b6-a6d8-ad90fadf701b

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 10 (40+m.val),
      RHDirect132Integer.gammaIm 10 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 2 []).getD (40+m.val) (0,0)) := by
  decide +kernel
