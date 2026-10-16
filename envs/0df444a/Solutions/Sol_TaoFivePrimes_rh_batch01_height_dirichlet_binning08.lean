-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:03:10.234976+00:00
-- url     : https://prove2.me/submissions/5ac64aaf-3234-46d6-8de3-0f41256dc392

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues08
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins08
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues08.rows.flatten=
    RHBatch01DirichletBins08.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
