-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_6_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:15:02.766489+00:00
-- url     : https://prove2.me/submissions/e34a9221-5b1e-40ee-ad46-2114f8fefa0f

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 6 (0+m.val),
      RHDirect132Integer.gammaIm 6 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 2 []).getD (0+m.val) (0,0)) := by
  decide +kernel
