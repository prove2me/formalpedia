-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:17:33.013443+00:00
-- url     : https://prove2.me/submissions/7ce715cd-2d17-4d04-9c35-988cf35ff56c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues08
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins08
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues08.rows.flatten=
    RHHighDirichletBins08.values.map RHHighDirichletBinning.decode := by decide +kernel
