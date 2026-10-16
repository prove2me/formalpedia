-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning27
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:57:25.96588+00:00
-- url     : https://prove2.me/submissions/6cd36f3f-3d3f-4478-b4b8-766c39a27d23

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues27
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins27
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues27.rows.flatten=
    RHBatch01DirichletBins27.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
