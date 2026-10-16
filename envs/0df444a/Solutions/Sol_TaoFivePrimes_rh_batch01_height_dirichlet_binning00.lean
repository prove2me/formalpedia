-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:14:06.822463+00:00
-- url     : https://prove2.me/submissions/c1dc64dd-9375-4bab-ad82-fb5c315602ac

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues00
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins00
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues00.rows.flatten=
    RHBatch01DirichletBins00.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
