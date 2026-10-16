-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_phase_input_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:11:15.046106+00:00
-- url     : https://prove2.me/submissions/34234a51-e6bb-4834-a759-33eeb4728340

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelUniformPhase
open RHFastKernelGammaArithmetic RHFastKernelLogData
lemma phase_input_bound (ii : Int) :
  2*((ii*10^50-2*(P:Int)*((ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int)))*(D:Int)).natAbs/(8*10^50))≤D := by
  have h0 := Int.emod_nonneg (ii*10^50+(P:Int)*(D:Int)) (by norm_num [P,D] : (2*(P:Int)*(D:Int))≠0)
  have h1 := Int.emod_lt_of_pos (ii*10^50+(P:Int)*(D:Int)) (by norm_num [P,D] : (0:Int)<2*(P:Int)*(D:Int))
  have he := Int.emod_add_ediv_mul (ii*10^50+(P:Int)*(D:Int)) (2*(P:Int)*(D:Int))
  norm_num [P,D] at *
  omega
end RHFastKernelUniformPhase

theorem solution (T i : Nat) :
  2*(RHFastKernelGammaArithmetic.compute T i).phaseInput≤RHFastKernelLogData.D := by
  exact RHFastKernelUniformPhase.phase_input_bound (RHFastKernelGammaArithmetic.compute T i).phase
#print axioms solution
