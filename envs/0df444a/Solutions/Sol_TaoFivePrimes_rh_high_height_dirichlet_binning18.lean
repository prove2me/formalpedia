-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning18
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:19:58.580874+00:00
-- url     : https://prove2.me/submissions/4357ffff-7bd8-404f-8c47-940650cc3cfd

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues18
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins18
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues18.rows.flatten=
    RHHighDirichletBins18.values.map RHHighDirichletBinning.decode := by decide +kernel
