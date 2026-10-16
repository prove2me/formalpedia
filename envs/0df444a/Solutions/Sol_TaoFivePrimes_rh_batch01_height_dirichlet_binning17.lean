-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning17
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:32:56.197547+00:00
-- url     : https://prove2.me/submissions/b93943d1-4c11-472d-9b07-7560eb066b57

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues17
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins17
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues17.rows.flatten=
    RHBatch01DirichletBins17.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
