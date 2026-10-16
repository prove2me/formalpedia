-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_frequency0869_arithmetic_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:59:47.61469+00:00
-- url     : https://prove2.me/submissions/20b3697b-2fd6-41aa-b41d-c6381928241b

import Definitions.Def_TaoFivePrimes_RHFastWindowFrequency0869
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution : RHFastBallFrequencyChecker.valid 869
 RHFastWindowFrequency0869.anchor RHFastWindowFrequency0869.pi RHFastWindowFrequency0869.root RHFastWindowFrequency0869.omega RHFastWindowFrequency0869.qs RHFastWindowFrequency0869.factors RHFastWindowFrequency0869.hs RHFastWindowFrequency0869.es RHFastWindowFrequency0869.ss RHFastWindowFrequency0869.reference=true := by decide +kernel
#print axioms solution
