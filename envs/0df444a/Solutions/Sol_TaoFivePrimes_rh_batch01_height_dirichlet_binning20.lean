-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning20
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:53:15.078989+00:00
-- url     : https://prove2.me/submissions/57dc924d-e9c6-4276-bff0-10ec5cb52a7b

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues20
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins20
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues20.rows.flatten=
    RHBatch01DirichletBins20.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
