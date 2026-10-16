-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_dirichlet_binning31
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T21:54:11.437245+00:00
-- url     : https://prove2.me/submissions/6b181671-76b3-498f-82d0-354477cac73a

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues31
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins31
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution :
  RHHighDirichletBinning.bins RHBatch01DirichletValues31.rows.flatten=
    RHBatch01DirichletBins31.values.map RHHighDirichletBinning.decode := by decide +kernel
#print axioms solution
