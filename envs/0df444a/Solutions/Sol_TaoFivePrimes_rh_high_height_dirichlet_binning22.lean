-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning22
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:36:46.870539+00:00
-- url     : https://prove2.me/submissions/00cbe30e-08ca-4f1a-aa33-fa7d31ced52a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues22
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins22
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues22.rows.flatten=
    RHHighDirichletBins22.values.map RHHighDirichletBinning.decode := by decide +kernel
