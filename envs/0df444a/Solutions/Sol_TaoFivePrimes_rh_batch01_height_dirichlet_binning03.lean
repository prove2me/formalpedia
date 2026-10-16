-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:32:08.745548+00:00
-- url     : https://prove2.me/submissions/f0e5e6a3-406e-42e8-b3b6-f972be28ab71

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues03
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins03
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues03.rows.flatten=
    RHBatch01DirichletBins03.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
