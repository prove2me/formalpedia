-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_14_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:18:55.018432+00:00
-- url     : https://prove2.me/submissions/69cddb50-6fa6-4602-b933-1dad7f34f665

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 14 (0+m.val),
      RHDirect132Integer.gammaIm 14 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData3.getD 2 []).getD (0+m.val) (0,0)) := by
  decide +kernel
