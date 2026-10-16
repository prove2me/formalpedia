-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning02
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:17:45.558842+00:00
-- url     : https://prove2.me/submissions/bcf5acd7-6ea5-4055-9b9d-06f844cfeaee

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues02
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins02
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues02.rows.flatten=
    RHBatch01DirichletBins02.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
