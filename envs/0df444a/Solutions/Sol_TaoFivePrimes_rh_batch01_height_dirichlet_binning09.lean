-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning09
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:43:55.085223+00:00
-- url     : https://prove2.me/submissions/bade49f0-424d-4707-8c75-bd8b165880ef

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues09
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins09
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues09.rows.flatten=
    RHBatch01DirichletBins09.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
