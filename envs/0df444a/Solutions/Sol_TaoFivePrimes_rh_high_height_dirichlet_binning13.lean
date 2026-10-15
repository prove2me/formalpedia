-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning13
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:42:12.229147+00:00
-- url     : https://prove2.me/submissions/fcfa6464-b1eb-468d-9f9a-6d0213e36730

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues13
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins13
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues13.rows.flatten=
    RHHighDirichletBins13.values.map RHHighDirichletBinning.decode := by decide +kernel
