-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:47:53.487307+00:00
-- url     : https://prove2.me/submissions/562e0024-8799-47aa-900b-c1b8d3cddf0c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues06
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins06
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues06.rows.flatten=
    RHBatch01DirichletBins06.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
