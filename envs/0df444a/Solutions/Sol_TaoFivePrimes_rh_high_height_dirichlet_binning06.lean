-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:08:49.445101+00:00
-- url     : https://prove2.me/submissions/71255143-a3fe-45f5-a804-2736adc6c86e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues06
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins06
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues06.rows.flatten=
    RHHighDirichletBins06.values.map RHHighDirichletBinning.decode := by decide +kernel
