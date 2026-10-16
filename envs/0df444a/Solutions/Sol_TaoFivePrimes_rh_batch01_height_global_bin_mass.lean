-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_global_bin_mass
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:25:26.042321+00:00
-- url     : https://prove2.me/submissions/8e82c5e8-143a-45b3-82f4-a0e0c2eb17f6

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01GlobalDirichletBins
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  RHBatch01GlobalDirichletBins.values.length=929 ∧
  ((RHBatch01GlobalDirichletBins.values.map (fun w=>
    ((RHHighDirichletBinning.decodeCoefficients 24 w).map (fun p=>p.1.natAbs+p.2.natAbs)).sum)).sum)≤100*2^128 := by decide +kernel
#print axioms solution
