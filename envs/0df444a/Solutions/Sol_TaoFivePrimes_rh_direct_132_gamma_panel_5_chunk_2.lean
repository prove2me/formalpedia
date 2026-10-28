-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_5_chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:14:49.403594+00:00
-- url     : https://prove2.me/submissions/eb210d88-c7fb-49a0-b21c-0c37db46b249

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 5 (40+m.val),
      RHDirect132Integer.gammaIm 5 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 1 []).getD (40+m.val) (0,0)) := by
  decide +kernel
