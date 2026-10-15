-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:02:24.857107+00:00
-- url     : https://prove2.me/submissions/0d23d283-3b53-4288-9e8f-93cf25259127

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues05
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins05
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues05.rows.flatten=
    RHHighDirichletBins05.values.map RHHighDirichletBinning.decode := by decide +kernel
