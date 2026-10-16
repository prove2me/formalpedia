-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:46:39.028584+00:00
-- url     : https://prove2.me/submissions/de6c002a-6852-495f-a1ce-5bad2316a415

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues11
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins11
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues11.rows.flatten=
    RHBatch01DirichletBins11.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
