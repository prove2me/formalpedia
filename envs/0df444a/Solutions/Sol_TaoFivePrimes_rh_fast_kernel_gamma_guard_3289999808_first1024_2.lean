-- Prove2me | solution 2 for TaoFivePrimes.rh_fast_kernel_gamma_guard_3289999808_first1024
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:55:58.074281+00:00
-- url     : https://prove2.me/submissions/60422eb6-6701-4e1a-a34c-02ee91ec2cee

import Mathlib.Data.List.Range
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHFastDirectGammaPilot
theorem checked : (List.range 1024).all (fun i =>
    RHFastKernelGammaGuards.guard
      (RHFastKernelGammaArithmetic.compute 3289999808 i)) = true := by
  decide +kernel
end RHFastDirectGammaPilot
theorem solution : ∀ i : Nat, 0 ≤ i → i < 1024 →
    RHFastKernelGammaGuards.guard
      (RHFastKernelGammaArithmetic.compute 3289999808 i) = true := by
  intro i _ hi
  exact List.all_eq_true.mp RHFastDirectGammaPilot.checked i (List.mem_range.mpr hi)
#print axioms solution
