-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning16
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:26:27.330067+00:00
-- url     : https://prove2.me/submissions/08b537cf-c613-49fd-8ed5-acd21b8e6b55

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues16
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins16
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues16.rows.flatten=
    RHBatch01DirichletBins16.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
