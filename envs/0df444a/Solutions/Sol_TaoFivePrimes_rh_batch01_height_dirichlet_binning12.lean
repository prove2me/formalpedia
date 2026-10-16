-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning12
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:53:02.494997+00:00
-- url     : https://prove2.me/submissions/7318423c-78ec-4fe9-b38a-fdb40a32d17c

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues12
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins12
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues12.rows.flatten=
    RHBatch01DirichletBins12.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
