-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning16
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:08:15.576555+00:00
-- url     : https://prove2.me/submissions/d7cbd982-7e59-4a0e-9405-136c69ef026b

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues16
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins16
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues16.rows.flatten=
    RHHighDirichletBins16.values.map RHHighDirichletBinning.decode := by decide +kernel
