-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning21
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:31:59.00215+00:00
-- url     : https://prove2.me/submissions/014d3bae-35d0-4d67-a06a-ed7068c6048c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues21
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins21
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues21.rows.flatten=
    RHHighDirichletBins21.values.map RHHighDirichletBinning.decode := by decide +kernel
