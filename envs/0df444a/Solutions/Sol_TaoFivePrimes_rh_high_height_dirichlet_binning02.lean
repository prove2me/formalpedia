-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T03:47:00.139821+00:00
-- url     : https://prove2.me/submissions/a270ee21-9bcf-442c-9b9c-4eccffbb752e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues02
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins02
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues02.rows.flatten=
    RHHighDirichletBins02.values.map RHHighDirichletBinning.decode := by decide +kernel
