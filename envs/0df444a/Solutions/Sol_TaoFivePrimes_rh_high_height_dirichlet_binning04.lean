-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_binning04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T03:56:52.088446+00:00
-- url     : https://prove2.me/submissions/ef7aa387-783a-492a-88a5-6472816495cf

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues04
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins04
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHHighDirichletValues04.rows.flatten=
    RHHighDirichletBins04.values.map RHHighDirichletBinning.decode := by decide +kernel
