-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning31
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:33:06.558042+00:00
-- url     : https://prove2.me/submissions/e4bde546-993a-4dcf-ade2-010f99177aab

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues31
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins31
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues31.rows.flatten=
    RHHighDirichletBins31.values.map RHHighDirichletBinning.decode := by decide +kernel
