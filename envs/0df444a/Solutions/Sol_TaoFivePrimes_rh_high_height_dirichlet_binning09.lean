-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning09
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:20:23.34912+00:00
-- url     : https://prove2.me/submissions/5dd72026-efee-4d78-aa2d-56f471fa666c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues09
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins09
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues09.rows.flatten=
    RHHighDirichletBins09.values.map RHHighDirichletBinning.decode := by decide +kernel
