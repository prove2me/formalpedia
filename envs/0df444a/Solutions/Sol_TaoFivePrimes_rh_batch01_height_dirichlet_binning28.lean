-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning28
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:22:37.846488+00:00
-- url     : https://prove2.me/submissions/573ceb48-8630-448c-ada9-6b10bef6b34b

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues28
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins28
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues28.rows.flatten=
    RHBatch01DirichletBins28.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
