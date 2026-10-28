-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_3_chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:13:37.860724+00:00
-- url     : https://prove2.me/submissions/742e5c70-b5b3-4a58-a98e-d661fcabef2d

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 3 (40+m.val),
      RHDirect132Integer.gammaIm 3 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 3 []).getD (40+m.val) (0,0)) := by
  decide +kernel
