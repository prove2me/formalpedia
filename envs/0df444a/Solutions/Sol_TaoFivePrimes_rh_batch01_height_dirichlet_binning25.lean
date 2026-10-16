-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning25
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:37:17.509913+00:00
-- url     : https://prove2.me/submissions/38836786-51b7-4336-8334-5b5d34a12354

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues25
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins25
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues25.rows.flatten=
    RHBatch01DirichletBins25.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
