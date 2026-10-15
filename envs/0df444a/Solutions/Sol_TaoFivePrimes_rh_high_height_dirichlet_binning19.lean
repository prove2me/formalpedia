-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning19
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:23:06.432196+00:00
-- url     : https://prove2.me/submissions/abe3cbe2-d902-4f84-b1ff-45072d549bfc

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues19
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins19
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues19.rows.flatten=
    RHHighDirichletBins19.values.map RHHighDirichletBinning.decode := by decide +kernel
