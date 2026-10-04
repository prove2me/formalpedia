-- Prove2me | solution 1 for ScenarioApproach.Generalization.binomial_sum_le_two_pow_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:36:42.057999+00:00
-- url     : https://prove2.me/submissions/efa50f6e-4a3c-4302-aefa-b8aff465296c

import Mathlib

set_option autoImplicit false

theorem solution (N d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) ≤
        2 ^ (d - 1) * (1 - ε / 2) ^ N ∧
      2 ^ (d - 1) * (1 - ε / 2) ^ N ≤ 2 ^ (d - 1) * Real.exp (-(ε / 2) * N) := by
  have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
  set g : ℕ → ℝ := fun i => (ε / 2) ^ i * (1 - ε) ^ (N - i) * (N.choose i : ℝ) with hg
  have hgnn : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; positivity
  have hsumg : ∑ i ∈ Finset.range d, g i ≤ (1 - ε / 2) ^ N := by
    have hbin : (1 - ε / 2) ^ N = ∑ i ∈ Finset.range (N + 1), g i := by
      have : (1 - ε / 2) = ε / 2 + (1 - ε) := by ring
      rw [this, add_pow]
    rw [hbin]
    by_cases hdN : d ≤ N + 1
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hdN)
        (fun i _ _ => hgnn i)
    · rw [not_le] at hdN
      refine le_of_eq (Finset.sum_subset (Finset.range_subset_range.mpr hdN.le) ?_).symm
      intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      simp only [hg, Nat.choose_eq_zero_of_lt (by omega : N < x), Nat.cast_zero, mul_zero]
  have hterm : ∀ i ∈ Finset.range d,
      (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) ≤ 2 ^ (d - 1) * g i := by
    intro i hi
    have hid : i ≤ d - 1 := by simp only [Finset.mem_range] at hi; omega
    have h2 : (2 : ℝ) ^ i ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) hid
    have he : ε ^ i = 2 ^ i * (ε / 2) ^ i := by
      rw [← mul_pow]; congr 1; ring
    simp only [hg]
    rw [he]
    have hA : 0 ≤ (ε / 2) ^ i * (1 - ε) ^ (N - i) * (N.choose i : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hA]
  refine ⟨?_, ?_⟩
  · calc ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)
        ≤ ∑ i ∈ Finset.range d, 2 ^ (d - 1) * g i := Finset.sum_le_sum hterm
      _ = 2 ^ (d - 1) * ∑ i ∈ Finset.range d, g i := by rw [Finset.mul_sum]
      _ ≤ 2 ^ (d - 1) * (1 - ε / 2) ^ N :=
          mul_le_mul_of_nonneg_left hsumg (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hx : 1 - ε / 2 ≤ Real.exp (-(ε / 2)) := by
      have := Real.add_one_le_exp (-(ε / 2)); linarith
    have h0 : 0 ≤ 1 - ε / 2 := by linarith
    calc (1 - ε / 2) ^ N ≤ Real.exp (-(ε / 2)) ^ N := pow_le_pow_left₀ h0 hx N
      _ = Real.exp (-(ε / 2) * N) := by
        rw [← Real.exp_nat_mul]; ring_nf
