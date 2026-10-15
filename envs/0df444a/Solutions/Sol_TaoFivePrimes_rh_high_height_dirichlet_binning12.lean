-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning12
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T04:41:31.968476+00:00
-- url     : https://prove2.me/submissions/d9a248bc-c240-4c01-b419-97c1816eff6d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues12
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins12
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues12.rows.flatten=
    RHHighDirichletBins12.values.map RHHighDirichletBinning.decode := by decide +kernel
