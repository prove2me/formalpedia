-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning30
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:25:22.072071+00:00
-- url     : https://prove2.me/submissions/e31702e5-a8c0-4f5f-879e-b06d7827a706

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues30
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins30
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues30.rows.flatten=
    RHHighDirichletBins30.values.map RHHighDirichletBinning.decode := by decide +kernel
