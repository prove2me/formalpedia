-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning10
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:23:58.979851+00:00
-- url     : https://prove2.me/submissions/7f210ec3-161f-4512-98e4-e32a67951c7c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues10
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins10
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues10.rows.flatten=
    RHHighDirichletBins10.values.map RHHighDirichletBinning.decode := by decide +kernel
