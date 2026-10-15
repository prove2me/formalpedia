-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning29
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:17:15.691271+00:00
-- url     : https://prove2.me/submissions/dbaa8819-635e-4401-a814-be9e9bed87ae

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues29
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins29
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues29.rows.flatten=
    RHHighDirichletBins29.values.map RHHighDirichletBinning.decode := by decide +kernel
