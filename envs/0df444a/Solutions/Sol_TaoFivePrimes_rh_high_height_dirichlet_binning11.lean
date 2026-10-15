-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:27:35.91845+00:00
-- url     : https://prove2.me/submissions/14dfdf87-e231-4497-8f03-4c5376084c17

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues11
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins11
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues11.rows.flatten=
    RHHighDirichletBins11.values.map RHHighDirichletBinning.decode := by decide +kernel
