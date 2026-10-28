-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_gamma_panel_10_chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:16:58.219578+00:00
-- url     : https://prove2.me/submissions/b1c20db3-ba89-4212-b451-a57dde723fe0

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 10 (0+m.val),
      RHDirect132Integer.gammaIm 10 (0+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 2 []).getD (0+m.val) (0,0)) := by
  decide +kernel
