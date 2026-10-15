-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:12:57.475073+00:00
-- url     : https://prove2.me/submissions/8c778879-8a58-419d-9092-062da2cf48a5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues07
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues07.rows.flatten=
    RHHighDirichletBins07.values.map RHHighDirichletBinning.decode := by decide +kernel
