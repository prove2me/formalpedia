-- Prove2me | solution 1 for P2M_GlobalTheory_TraceExpSmul_trace_mul_exp_smul__ab68fdf078d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:20.291005+00:00
-- url     : https://prove2.me/submissions/a4fa7578-48c6-47ac-b80d-755c1b64f058

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero
import Theorems.Thm_GlobalTheory_TraceExpSmul_trace_R_mul_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceExpSmul
open Finset
variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]
namespace GlobalTheory.TraceExpSmul
namespace trace_mul_exp_smul
theorem _root_.solution.{u, v} : ∀ {K : Type u} {n : Type v} [inst : Field K] [inst_1 : CharZero K] [inst_2 : Fintype n] [inst_3 : DecidableEq n] {R N : Matrix n n K}, IsNilpotent N → ∀ {d : K}, N * R = d • (R * N) → ∀ (s : K), Matrix.trace (R * IsNilpotent.exp (s • N)) = Matrix.trace R := by
  intro K n _ _ _ _ R N hN d h s
  obtain ⟨p, hp⟩ := id hN
  have hsN : (s • N) ^ (p + 1) = 0 := by
    rw [smul_pow, pow_succ N, hp, zero_mul, smul_zero]
  rw [IsNilpotent.exp_eq_sum hsN, mul_sum, Matrix.trace_sum, sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, mul_one]
  rw [add_eq_right]
  refine sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul, smul_pow, mul_smul_comm, Matrix.trace_smul,
    trace_R_mul_pow_eq_zero hN h (i + 1) (by omega), smul_zero, smul_zero]
end trace_mul_exp_smul
end GlobalTheory.TraceExpSmul
