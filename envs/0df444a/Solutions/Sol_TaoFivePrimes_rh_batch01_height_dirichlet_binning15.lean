-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning15
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:19:34.466006+00:00
-- url     : https://prove2.me/submissions/419ba4f5-ca40-4428-9a28-48dd77e537cc

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues15
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins15
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues15.rows.flatten=
    RHBatch01DirichletBins15.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
