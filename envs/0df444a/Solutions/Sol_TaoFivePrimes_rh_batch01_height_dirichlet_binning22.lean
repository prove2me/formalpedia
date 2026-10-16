-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning22
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:07:01.778983+00:00
-- url     : https://prove2.me/submissions/b8e84380-69d7-4a01-9ccd-180260903618

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues22
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins22
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues22.rows.flatten=
    RHBatch01DirichletBins22.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
