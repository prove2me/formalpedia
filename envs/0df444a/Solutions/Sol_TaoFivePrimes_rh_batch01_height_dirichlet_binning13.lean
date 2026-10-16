-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning13
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:00:46.451559+00:00
-- url     : https://prove2.me/submissions/db6d08f7-65ae-48f1-a78b-5340f40a8b13

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues13
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins13
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues13.rows.flatten=
    RHBatch01DirichletBins13.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
