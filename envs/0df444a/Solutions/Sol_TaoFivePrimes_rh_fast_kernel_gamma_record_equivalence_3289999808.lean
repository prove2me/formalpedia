-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_record_equivalence_3289999808
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:03:35.386269+00:00
-- url     : https://prove2.me/submissions/9033f669-9faf-4ae2-99e9-daa1e8cfc7f1

import Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem solution : ∀ i : Nat, (let v := RHFastKernelGammaArithmetic.compute 3289999808 i; (⟨v.logu,v.realPart,v.phase,v.period,v.phaseInput,v.negative,v.expInput,v.cos,v.sin,v.expSeed,v.amplitude,v.gammaRe,v.gammaIm⟩ : RHBatch01GammaArithmetic.Record))=RHBatch01GammaArithmetic.compute i := by
 intro i
 rfl
#print axioms solution
