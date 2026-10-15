-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:44:09.445809+00:00
-- url     : https://prove2.me/submissions/91a78267-d2c1-4da9-8136-906cf204d82a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues23
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins23
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues23.rows.flatten=
    RHHighDirichletBins23.values.map RHHighDirichletBinning.decode := by decide +kernel
