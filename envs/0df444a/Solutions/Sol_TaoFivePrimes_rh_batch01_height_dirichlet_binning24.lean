-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning24
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:25:06.6034+00:00
-- url     : https://prove2.me/submissions/492dfb2e-875d-4174-950a-116702845ada

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues24
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins24
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues24.rows.flatten=
    RHBatch01DirichletBins24.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
