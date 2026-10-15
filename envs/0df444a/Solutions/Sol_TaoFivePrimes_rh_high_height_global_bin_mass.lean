-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_global_bin_mass
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:13:33.15512+00:00
-- url     : https://prove2.me/submissions/8f25edc8-5390-4952-a567-b7fd2363922f

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighGlobalDirichletBins
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
  RHHighGlobalDirichletBins.values.length=929 ∧
  ((RHHighGlobalDirichletBins.values.map (fun w=>
    ((RHHighDirichletBinning.decodeCoefficients 24 w).map (fun p=>p.1.natAbs+p.2.natAbs)).sum)).sum)≤100*2^128 := by decide +kernel
