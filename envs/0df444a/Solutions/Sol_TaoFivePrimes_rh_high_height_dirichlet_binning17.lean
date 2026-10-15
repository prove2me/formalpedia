-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning17
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:13:02.983127+00:00
-- url     : https://prove2.me/submissions/ad5fd309-be28-43c0-9182-e5fb261c6c2f

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues17
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins17
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues17.rows.flatten=
    RHHighDirichletBins17.values.map RHHighDirichletBinning.decode := by decide +kernel
