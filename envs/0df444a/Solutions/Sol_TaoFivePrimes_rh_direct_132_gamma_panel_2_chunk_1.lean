-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_2_chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:12:53.062581+00:00
-- url     : https://prove2.me/submissions/abed2142-eb8f-4523-a882-11b0f4b2b81a

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 2 (20+m.val),
      RHDirect132Integer.gammaIm 2 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 2 []).getD (20+m.val) (0,0)) := by
  decide +kernel
