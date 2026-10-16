-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:37:06.990508+00:00
-- url     : https://prove2.me/submissions/9ac40507-bddc-4502-b863-ab2188e0f483

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues04
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins04
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues04.rows.flatten=
    RHBatch01DirichletBins04.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
