-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_13_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:18:40.780625+00:00
-- url     : https://prove2.me/submissions/08ea9a38-6c13-4f12-819c-e5254cae817a

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 13 (20+m.val),
      RHDirect132Integer.gammaIm 13 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData3.getD 1 []).getD (20+m.val) (0,0)) := by
  decide +kernel
