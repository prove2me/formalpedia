-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_4_chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:14:18.986386+00:00
-- url     : https://prove2.me/submissions/1855ba4b-10e6-46f1-a641-4254bfdd028b

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 4 (40+m.val),
      RHDirect132Integer.gammaIm 4 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData1.getD 0 []).getD (40+m.val) (0,0)) := by
  decide +kernel
