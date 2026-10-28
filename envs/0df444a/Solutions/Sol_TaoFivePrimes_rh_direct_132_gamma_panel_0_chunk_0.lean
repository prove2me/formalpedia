-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_0_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:09:25.256244+00:00
-- url     : https://prove2.me/submissions/a4952b60-18c1-4d89-b8c2-3c24ca7ebe13

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 0 (0+m.val),
      RHDirect132Integer.gammaIm 0 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 0 []).getD (0+m.val) (0,0)) := by
  decide +kernel
