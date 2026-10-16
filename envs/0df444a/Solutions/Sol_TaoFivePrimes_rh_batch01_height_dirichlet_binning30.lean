-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning30
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:43:34.491031+00:00
-- url     : https://prove2.me/submissions/92a00dcf-74a2-4420-955f-e64bc87bd5c6

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues30
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins30
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues30.rows.flatten=
    RHBatch01DirichletBins30.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
