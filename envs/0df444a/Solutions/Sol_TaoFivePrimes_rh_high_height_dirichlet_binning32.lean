-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning32
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T06:36:27.359873+00:00
-- url     : https://prove2.me/submissions/0bd8481d-fff7-4733-9e35-2203a9060e8d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues32
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins32
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues32.rows.flatten=
    RHHighDirichletBins32.values.map RHHighDirichletBinning.decode := by decide +kernel
