-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:57:51.179674+00:00
-- url     : https://prove2.me/submissions/28c98faa-1ad0-43ae-8194-3718885c4355

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues07
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins07
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues07.rows.flatten=
    RHBatch01DirichletBins07.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
