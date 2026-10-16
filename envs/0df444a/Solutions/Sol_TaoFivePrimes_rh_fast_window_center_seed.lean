-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window_center_seed
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:36:10.84161+00:00
-- url     : https://prove2.me/submissions/816c83c7-6551-493b-bb5a-10a1fe0df9fb

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
theorem solution :
 let a:=RHFastKernelGammaArithmetic.compute 3289999936 8192
 (a.cos,a.sin,a.amplitude,a.negative)=(338465131998480615193183972069514375853,35120416548886332677381057571856482336,4235336350958928456860515144971299982,false) := by decide +kernel
#print axioms solution
