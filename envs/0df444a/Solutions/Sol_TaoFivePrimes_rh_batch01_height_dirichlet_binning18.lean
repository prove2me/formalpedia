-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning18
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:40:15.075474+00:00
-- url     : https://prove2.me/submissions/18fed290-dabc-4401-b1bb-e38e36540acd

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues18
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins18
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues18.rows.flatten=
    RHBatch01DirichletBins18.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
