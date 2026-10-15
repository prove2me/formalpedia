-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:58:44.356757+00:00
-- url     : https://prove2.me/submissions/13ce9e23-d598-433a-85a0-51eedec3957d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues14
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins14
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues14.rows.flatten=
    RHHighDirichletBins14.values.map RHHighDirichletBinning.decode := by decide +kernel
