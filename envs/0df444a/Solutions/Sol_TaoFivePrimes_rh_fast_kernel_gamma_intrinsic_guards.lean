-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_intrinsic_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:04:45.09243+00:00
-- url     : https://prove2.me/submissions/a939e9ce-3ceb-46cf-9429-387fa4eef608

import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_base_guards
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_trig_guards
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_exp_guards
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner

theorem solution (T i : Nat) (hT : 257≤T) (hU : T≤4294967040) (hi : i<16384) :
    (compute T i).realPart≤0 ∧
    -100*(D:Int)≤(compute T i).realPart ∧
    (compute T i).period.natAbs≤10000000000 ∧
    2*(compute T i).phaseInput≤D ∧
    2*(compute T i).expInput≤D ∧
    (compute T i).phaseInput^2*horner (cn D) ((compute T i).phaseInput^4)≤
      horner (cp D) ((compute T i).phaseInput^4) ∧
    (compute T i).phaseInput^2*horner (sn D) ((compute T i).phaseInput^4)≤
      horner (sp D) ((compute T i).phaseInput^4) ∧
    0<(compute T i).cos ∧
    0<(compute T i).expSeed ∧
    (compute T i).expSeed≤D ∧ (compute T i).amplitude≤D := by
  have hb := TaoFivePrimes.rh_fast_kernel_gamma_base_guards T i hT hU hi
  have ht := TaoFivePrimes.rh_fast_kernel_gamma_trig_guards
    (compute T i).phaseInput hb.2.2.2.1
  have he := TaoFivePrimes.rh_fast_kernel_gamma_exp_guards
    (compute T i).expInput hb.2.2.2.2
  exact ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2,
    ht.1,ht.2.1,ht.2.2,he.1,he.2.1,he.2.2 8⟩
#print axioms solution
