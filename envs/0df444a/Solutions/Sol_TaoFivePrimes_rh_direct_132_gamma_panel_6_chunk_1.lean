-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_6_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:15:13.063668+00:00
-- url     : https://prove2.me/submissions/2c18c392-5c84-410a-97cb-d7859f9eced0

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 6 (20+m.val),
      RHDirect132Integer.gammaIm 6 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 2 []).getD (20+m.val) (0,0)) := by
  decide +kernel
