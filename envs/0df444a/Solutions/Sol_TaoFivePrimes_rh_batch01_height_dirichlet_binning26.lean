-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning26
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:44:05.280078+00:00
-- url     : https://prove2.me/submissions/871c392f-dcf4-4796-871a-ce3429b775cb

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues26
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins26
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues26.rows.flatten=
    RHBatch01DirichletBins26.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
