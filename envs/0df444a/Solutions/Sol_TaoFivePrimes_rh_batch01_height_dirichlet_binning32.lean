-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning32
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:01:21.847909+00:00
-- url     : https://prove2.me/submissions/a2569c09-9083-4724-bb96-2b8f5a85ac01

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues32
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins32
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues32.rows.flatten=
    RHBatch01DirichletBins32.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
