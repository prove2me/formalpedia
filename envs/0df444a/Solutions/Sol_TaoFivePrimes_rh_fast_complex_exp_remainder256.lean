-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_complex_exp_remainder256
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:34:54.165521+00:00
-- url     : https://prove2.me/submissions/f58c855e-1c3b-45a2-9ec4-ebb61da1e634

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastExp256RemainderProof
lemma exp_factorial_remainder (z : ℂ) (n : Nat) :
    ‖Complex.exp z-∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤
      (‖z‖^n/(n.factorial:ℝ))*Real.exp ‖z‖ := by
  rw [←CauSeq.lim_const (abv:=norm) (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)),
    Complex.exp,sub_eq_add_neg,←CauSeq.lim_neg]
  rw [CauSeq.lim_add (Complex.exp' z) (-CauSeq.const norm (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ))),
    ←Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n,fun j hj => ?_⟩)
  simp_rw [←sub_eq_add_neg]
  change ‖(∑ k ∈ Finset.range j, z^k/(k.factorial:ℂ))-
    ∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤_
  let m := j-n
  have he : j=n+m := (Nat.add_sub_of_le hj).symm
  rw [he,Finset.sum_range_add_sub_sum_range]
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖z^(n+k)/((n+k).factorial:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (‖z‖^n/(n.factorial:ℝ))*(‖z‖^k/(k.factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_div,Complex.norm_pow,norm_natCast,pow_add,norm_mul]
      rw [div_mul_div_comm]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
    _ = (‖z‖^n/(n.factorial:ℝ))*(∑ k ∈ Finset.range m, ‖z‖^k/(k.factorial:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg z) m) (by positivity)
lemma bound (z:ℂ) (hz:‖z‖≤1/16) :
 ‖Complex.exp z-∑k∈Finset.range 41,z^k/(k.factorial:ℂ)‖≤1/(2:ℝ)^256 := by
 have hp:=pow_le_pow_left₀ (norm_nonneg z) hz 41
 have he:Real.exp ‖z‖≤3 := (Real.exp_le_exp.mpr (by linarith)).trans Real.exp_one_lt_three.le
 apply (exp_factorial_remainder z 41).trans
 calc
  _ ≤ ((1/16:ℝ)^41/(41:Nat).factorial)*3 :=
   mul_le_mul (div_le_div_of_nonneg_right hp (by positivity)) he (by positivity) (by positivity)
  _ ≤ _ := by norm_num [Nat.factorial]
end RHFastExp256RemainderProof

theorem solution (z:ℂ) (hz:‖z‖≤1/16) :
 ‖Complex.exp z-∑k∈Finset.range 41,z^k/(k.factorial:ℂ)‖≤1/(2:ℝ)^256 := RHFastExp256RemainderProof.bound z hz
#print axioms solution
