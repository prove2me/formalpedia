-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_log_seed_program_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:08:51.025128+00:00
-- url     : https://prove2.me/submissions/710a4e1d-7b10-4b20-94b2-2cc3aaca5a9d

import Definitions.Def_TaoFivePrimes_RHFastBallSeedPrograms
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 (RHFastBallSeedPrograms.logRatio 2 1,RHFastBallSeedPrograms.logRatio 3289999936 (2^31))=
 (⟨235865763225513294137944142764154484396,0,11⟩,⟨145161321996686247491177286792996021954,0,11⟩) := by decide +kernel
#print axioms solution
