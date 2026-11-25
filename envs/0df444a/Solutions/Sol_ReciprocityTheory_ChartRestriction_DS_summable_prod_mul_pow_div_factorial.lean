-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.summable_prod_mul_pow_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:28.675549+00:00
-- url     : https://prove2.me/submissions/77d41bf1-efdd-4a93-8195-27bcb533150e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Series

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hrB : r * B < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ) := by
  set q : ℝ := (1 + r * B) / 2 with hq_def
  have hq1 : q < 1 := by rw [hq_def]; linarith
  have hd : 0 < q - r * B := by rw [hq_def]; linarith
  have hq0 : 0 ≤ q := by rw [hq_def]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (((A + B * k) * r) / (q - r * B))
  have hterm : ∀ i : ℕ, 0 ≤ A + B * ((k : ℝ) + i) := fun i =>
    add_nonneg hA (mul_nonneg hB (by positivity))
  have hf : ∀ m : ℕ, 0 ≤ (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ) :=
    fun m => div_nonneg (mul_nonneg (prod_nonneg fun i _ => hterm i) (pow_nonneg hr _)) (by positivity)
  refine summable_of_ratio_norm_eventually_le hq1 ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  rw [Real.norm_of_nonneg (hf _), Real.norm_of_nonneg (hf _)]
  have hx : (A + B * ((k : ℝ) + m)) * r ≤ q * ((m : ℝ) + 1) := by
    have h0 := (div_le_iff₀ hd).1 hN
    have hmN : (N : ℝ) ≤ m := by exact_mod_cast hm
    have h1 : (A + B * k) * r ≤ (q - r * B) * m := by nlinarith
    nlinarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  rw [prod_range_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have key : (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * (A + B * ((k : ℝ) + m)) * (r ^ m * r) /
      (((m : ℝ) + 1) * (m.factorial : ℝ)) =
      ((∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ)) *
        ((A + B * ((k : ℝ) + m)) * r / ((m : ℝ) + 1)) := by
    field_simp
  rw [key, mul_comm q]
  apply mul_le_mul_of_nonneg_left _ (hf m)
  rw [div_le_iff₀ hm1]
  exact hx
end ReciprocityTheory.ChartRestriction.DS
