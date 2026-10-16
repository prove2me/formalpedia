-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:16:06.428473+00:00
-- url     : https://prove2.me/submissions/4446f30e-619d-4425-b250-271eb5ce879a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues01
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins01
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues01.rows.flatten=
    RHBatch01DirichletBins01.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
