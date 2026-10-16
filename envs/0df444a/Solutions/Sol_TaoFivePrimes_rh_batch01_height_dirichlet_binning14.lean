-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:10:58.540985+00:00
-- url     : https://prove2.me/submissions/bca827c4-35b7-4153-9735-5ad8936c793e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues14
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins14
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues14.rows.flatten=
    RHBatch01DirichletBins14.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
