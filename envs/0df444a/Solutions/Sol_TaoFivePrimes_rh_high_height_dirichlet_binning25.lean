-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning25
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:56:52.349559+00:00
-- url     : https://prove2.me/submissions/af82578b-8cbe-4ec5-a0c2-d33a2db2b088

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues25
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins25
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues25.rows.flatten=
    RHHighDirichletBins25.values.map RHHighDirichletBinning.decode := by decide +kernel
