-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning28
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:09:54.193008+00:00
-- url     : https://prove2.me/submissions/7625f6d1-fae0-4653-8884-fa15db86fdb5

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues28
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins28
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues28.rows.flatten=
    RHHighDirichletBins28.values.map RHHighDirichletBinning.decode := by decide +kernel
