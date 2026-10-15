-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T03:46:26.346448+00:00
-- url     : https://prove2.me/submissions/0aa35028-d6f9-4291-8c71-c0ef566d708f

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues01
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins01
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues01.rows.flatten=
    RHHighDirichletBins01.values.map RHHighDirichletBinning.decode := by decide +kernel
