-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_guard_equivalence_3289999808
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T16:53:41.899333+00:00
-- url     : https://prove2.me/submissions/8093c44a-4d1a-4f00-a238-4328faedece7

import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution : ∀ i : Nat, RHBatch01GammaGuards.guard (RHBatch01GammaArithmetic.compute i)=RHFastKernelGammaGuards.guard (RHFastKernelGammaArithmetic.compute 3289999808 i) := by
 intro i
 rfl
#print axioms solution
