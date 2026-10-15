-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T03:37:37.579986+00:00
-- url     : https://prove2.me/submissions/285a7086-480f-41cd-a125-33fab5c7ab0a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues00
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins00
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues00.rows.flatten=
    RHHighDirichletBins00.values.map RHHighDirichletBinning.decode := by decide +kernel
