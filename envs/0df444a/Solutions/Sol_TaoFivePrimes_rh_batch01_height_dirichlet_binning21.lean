-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning21
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:58:50.394667+00:00
-- url     : https://prove2.me/submissions/3d61668e-bf7d-42eb-8d99-fbc9c8b30a4d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues21
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins21
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues21.rows.flatten=
    RHBatch01DirichletBins21.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
