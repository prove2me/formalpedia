-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning29
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:34:52.570866+00:00
-- url     : https://prove2.me/submissions/5d5e4e9d-9d94-44c3-9668-373c47a8ab81

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues29
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins29
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues29.rows.flatten=
    RHBatch01DirichletBins29.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
