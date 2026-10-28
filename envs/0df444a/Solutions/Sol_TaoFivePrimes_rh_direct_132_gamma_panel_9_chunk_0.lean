-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_9_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:16:29.199831+00:00
-- url     : https://prove2.me/submissions/3894d8fa-e788-4f81-8b36-c9bd0fad9a70

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 9 (0+m.val),
      RHDirect132Integer.gammaIm 9 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 1 []).getD (0+m.val) (0,0)) := by
  decide +kernel
