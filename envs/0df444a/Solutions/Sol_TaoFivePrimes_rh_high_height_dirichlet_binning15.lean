-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning15
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:04:51.519262+00:00
-- url     : https://prove2.me/submissions/e52037c7-431f-4848-90bf-ede891b62dec

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues15
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins15
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues15.rows.flatten=
    RHHighDirichletBins15.values.map RHHighDirichletBinning.decode := by decide +kernel
