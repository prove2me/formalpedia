-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_4_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:14:05.217981+00:00
-- url     : https://prove2.me/submissions/2d1def9c-2713-40e9-9227-104e27d791b9

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 4 (20+m.val),
      RHDirect132Integer.gammaIm 4 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 0 []).getD (20+m.val) (0,0)) := by
  decide +kernel
