-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_setup_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:40:31.784406+00:00
-- url     : https://prove2.me/submissions/abe00b8b-454a-48a6-85ab-e19c4eaa9648

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastWindow256Common
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
open RHFastBallArithmetic

theorem solution :
 RHFastWindow256Common.inputs=RHFastWindow256Setup.inputs 3289999936 ∧
 RHFastWindow256Common.qs=RHFastWindow256Setup.coefficients 3289999936 ∧
 RHFastWindow256Common.pi=RHFastWindow256Setup.lift RHFastBallSeedPrograms.pi ∧
 RHFastWindow256Common.root=RHFastWindow256Setup.lift RHFastBallSeedPrograms.root ∧
 RHFastWindow256Common.omega=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.omega 3289999936) ∧
 RHFastWindow256Common.factors=RHFastWindow256Setup.factors RHFastWindow256Common.pi ∧
 RHFastWindow256Common.anchor=RHFastWindow256Setup.lift (RHFastBallSeedPrograms.anchor
  338465131998480615193183972069514375853 35120416548886332677381057571856482336 4235336350958928456860515144971299982 false) := by decide +kernel
#print axioms solution
