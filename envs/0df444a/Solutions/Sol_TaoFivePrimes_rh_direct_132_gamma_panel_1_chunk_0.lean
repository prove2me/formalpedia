-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_1_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:12:16.882493+00:00
-- url     : https://prove2.me/submissions/14e6ed06-ff8a-4b38-8a3f-4e73526b35df

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 1 (0+m.val),
      RHDirect132Integer.gammaIm 1 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 1 []).getD (0+m.val) (0,0)) := by
  decide +kernel
