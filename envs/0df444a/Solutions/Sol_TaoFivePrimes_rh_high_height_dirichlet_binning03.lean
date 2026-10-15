-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T03:56:13.263852+00:00
-- url     : https://prove2.me/submissions/e35a739b-24a5-4994-8beb-56df9f0c2d32

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues03
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins03
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues03.rows.flatten=
    RHHighDirichletBins03.values.map RHHighDirichletBinning.decode := by decide +kernel
