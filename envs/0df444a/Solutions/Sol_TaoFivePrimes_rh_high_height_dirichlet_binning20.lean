-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning20
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:30:04.513024+00:00
-- url     : https://prove2.me/submissions/650c5c74-60eb-4992-846a-bf3a8ef0f96c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues20
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins20
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues20.rows.flatten=
    RHHighDirichletBins20.values.map RHHighDirichletBinning.decode := by decide +kernel
