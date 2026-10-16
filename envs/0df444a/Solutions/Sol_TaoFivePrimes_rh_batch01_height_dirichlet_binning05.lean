-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:42:51.613843+00:00
-- url     : https://prove2.me/submissions/8bbf575b-123b-4574-856d-50b50db61b0d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues05
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins05
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues05.rows.flatten=
    RHBatch01DirichletBins05.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
