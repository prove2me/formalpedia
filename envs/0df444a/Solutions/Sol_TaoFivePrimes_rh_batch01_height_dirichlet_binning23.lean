-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:17:04.29862+00:00
-- url     : https://prove2.me/submissions/effae856-ddb8-4be1-8b25-c69815841a36

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues23
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins23
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues23.rows.flatten=
    RHBatch01DirichletBins23.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
