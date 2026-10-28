-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_14_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:19:00.658137+00:00
-- url     : https://prove2.me/submissions/c4f8300b-0024-4d34-89c1-1e91609f1d0b

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 14 (20+m.val),
      RHDirect132Integer.gammaIm 14 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData3.getD 2 []).getD (20+m.val) (0,0)) := by
  decide +kernel
