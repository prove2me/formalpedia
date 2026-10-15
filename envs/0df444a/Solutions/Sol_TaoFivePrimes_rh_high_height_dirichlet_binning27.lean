-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning27
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:05:17.340281+00:00
-- url     : https://prove2.me/submissions/0b0bad89-1f60-4c51-94ae-bee6ebb831ff

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues27
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins27
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues27.rows.flatten=
    RHHighDirichletBins27.values.map RHHighDirichletBinning.decode := by decide +kernel
