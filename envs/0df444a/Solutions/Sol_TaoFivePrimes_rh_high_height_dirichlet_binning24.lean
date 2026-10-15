-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning24
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:49:26.75899+00:00
-- url     : https://prove2.me/submissions/f6b285c6-f1e2-4d43-b5f4-af52e09d4c82

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues24
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins24
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues24.rows.flatten=
    RHHighDirichletBins24.values.map RHHighDirichletBinning.decode := by decide +kernel
