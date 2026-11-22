-- Prove2me | solution 1 for Pseudorandom.exp_le_one_add_add_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:40.176108+00:00
-- url     : https://prove2.me/submissions/bc511c51-6c1b-4976-86ad-6448e6c6dae5

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
open Nat
namespace Pseudorandom
theorem _root_.solution (x r : ℝ) (hx : |x| ≤ r) (hr : r < 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r)) := by
  have hE : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have ha1 : a < 1 := lt_of_le_of_lt hx hr
  have hG : HasSum (fun n : ℕ => a ^ n) (1 - a)⁻¹ := hasSum_geometric_of_lt_one ha0 ha1
  have hG2 : HasSum (fun n : ℕ => a ^ (n + 2) / 2) (a ^ 2 * (1 - a)⁻¹ / 2) := by
    have := (hG.mul_left (a ^ 2)).div_const 2
    simpa [pow_add, mul_comm] using this
  have hE2 : HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2) ! : ℝ))
      (Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i ! : ℝ)) :=
    (hasSum_nat_add_iff' 2).mpr hE
  have hle := hasSum_le (fun n => ?_) hE2 hG2
  · simp [Finset.sum_range_succ] at hle
    have h1 : a ^ 2 = x ^ 2 := by rw [ha, sq_abs]
    have h2 : a ^ 2 * (1 - a)⁻¹ / 2 ≤ x ^ 2 / (2 * (1 - r)) := by
      rw [h1, div_le_div_iff₀ (by norm_num) (by linarith), ← div_eq_mul_inv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    linarith
  · have hf : (2 : ℝ) ≤ ((n + 2) ! : ℝ) := by
      have : 2 ≤ (n + 2) ! := by
        calc 2 = (2 : ℕ) ! := rfl
          _ ≤ (n + 2) ! := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hxa : x ^ (n + 2) ≤ a ^ (n + 2) := by
      rw [ha, ← abs_pow]; exact le_abs_self _
    calc x ^ (n + 2) / ((n + 2) ! : ℝ) ≤ a ^ (n + 2) / ((n + 2) ! : ℝ) := by
          gcongr
      _ ≤ a ^ (n + 2) / 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hf
end Pseudorandom
