-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning26
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:00:28.418537+00:00
-- url     : https://prove2.me/submissions/cf2acf39-3818-41d6-886a-bb1adc45c37a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues26
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins26
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues26.rows.flatten=
    RHHighDirichletBins26.values.map RHHighDirichletBinning.decode := by decide +kernel
