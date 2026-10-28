-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_5_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:14:40.782985+00:00
-- url     : https://prove2.me/submissions/049faea1-f461-421b-84aa-d876e0cd4ff0

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 5 (20+m.val),
      RHDirect132Integer.gammaIm 5 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 1 []).getD (20+m.val) (0,0)) := by
  decide +kernel
