-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning19
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:46:28.284047+00:00
-- url     : https://prove2.me/submissions/4081e296-8b7e-4ad0-b79e-2e4f08d169b9

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues19
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins19
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues19.rows.flatten=
    RHBatch01DirichletBins19.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
