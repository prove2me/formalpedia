-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_7_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:15:31.34817+00:00
-- url     : https://prove2.me/submissions/f0d2e60c-ae5b-4476-b220-877cb9d21588

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 7 (0+m.val),
      RHDirect132Integer.gammaIm 7 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 3 []).getD (0+m.val) (0,0)) := by
  decide +kernel
