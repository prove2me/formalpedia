-- Prove2me | solution 1 for QuantumLTF.Majority.harmonic_kernel_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T02:57:58.323459+00:00
-- url     : https://prove2.me/submissions/40b80f0a-dec9-458d-b201-0209935ffba2

import Mathlib
namespace QuantumLTF.Majority

theorem harmonic_kernel_log_bound : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r → ∑ t : Fin (r+1), (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) ≤ H * Real.log r := by
  refine ⟨6, by norm_num, fun r hr => ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun t => (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ))) (r+1)]
  have h1 : ∀ t ∈ Finset.range (r+1), (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ))
      ≤ 1 / ((t : ℝ) + 1) + 1 / (((r - t : ℕ) : ℝ) + 1) := by
    intro t ht
    have htr : t ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have ha : (0:ℝ) < (t:ℝ) + 1 := by positivity
    have hb : (0:ℝ) < ((r - t : ℕ) : ℝ) + 1 := by positivity
    have hsum : ((t:ℝ) + 1) + (((r - t : ℕ) : ℝ) + 1) = (r:ℝ) + 2 := by
      rw [Nat.cast_sub htr]; ring
    push_cast
    rw [div_add_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos ha hb]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib]
  have hrefl : ∑ t ∈ Finset.range (r+1), 1 / (((r - t : ℕ) : ℝ) + 1)
      = ∑ t ∈ Finset.range (r+1), 1 / ((t : ℝ) + 1) := by
    have := Finset.sum_range_reflect (fun t => 1 / ((t : ℝ) + 1)) (r+1)
    simpa using this
  rw [hrefl]
  have hH : ∑ t ∈ Finset.range (r+1), 1 / ((t : ℝ) + 1) = (harmonic (r+1) : ℝ) := by
    simp [harmonic]
  rw [hH]
  have hle := harmonic_le_one_add_log (r+1)
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog1 : Real.log ((r:ℝ)+1) ≤ Real.log 2 + Real.log r := by
    rw [← Real.log_mul (by norm_num) hr0.ne']
    apply Real.log_le_log (by positivity)
    have : (1:ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    linarith
  have hl2 := Real.log_two_lt_d9
  have hlr : 1 < Real.log r := by
    rw [Real.lt_log_iff_exp_lt hr0]
    have := Real.exp_one_lt_d9
    have : (3:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  push_cast at hle
  linarith

end QuantumLTF.Majority

theorem solution : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r → ∑ t : Fin (r+1), (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) ≤ H * Real.log r :=
  QuantumLTF.Majority.harmonic_kernel_log_bound
