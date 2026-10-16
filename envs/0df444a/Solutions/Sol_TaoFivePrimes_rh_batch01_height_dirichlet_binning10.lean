-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning10
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:29:14.206237+00:00
-- url     : https://prove2.me/submissions/7bb0396f-eee3-418e-878e-03e6435f83c2

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues10
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins10
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues10.rows.flatten=
    RHBatch01DirichletBins10.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
