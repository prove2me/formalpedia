-- Prove2me | solution 1 for ScenarioApproach.Removal.binomial_sum_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:39:48.254247+00:00
-- url     : https://prove2.me/submissions/1211a452-6632-4319-bb9d-d89d86c6192b

import Mathlib



namespace ScenarioApproach.Removal

theorem bin_sum_le_core (N n : ℕ) (a ε : ℝ) (ha : 1 ≤ a) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∑ i ∈ Finset.range (n + 1), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) ≤
        a ^ n * (1 - (1 - 1 / a) * ε) ^ N := by
  have ha0 : 0 < a := by linarith
  set f : ℕ → ℝ := fun i => (N.choose i : ℝ) * (ε / a) ^ i * (1 - ε) ^ (N - i) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => by
    simp only [hf]; have : 0 ≤ 1 - ε := by linarith
    positivity
  have h1 : ∀ i ∈ Finset.range (n + 1),
      (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) ≤ a ^ n * f i := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hai : a ^ i ≤ a ^ n := pow_le_pow_right₀ ha hin
    have heq : (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) = a ^ i * f i := by
      simp only [hf]; rw [div_pow]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hai (hf0 i)
  calc ∑ i ∈ Finset.range (n + 1), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)
      ≤ ∑ i ∈ Finset.range (n + 1), a ^ n * f i := Finset.sum_le_sum h1
    _ = a ^ n * ∑ i ∈ Finset.range (n + 1), f i := by rw [Finset.mul_sum]
    _ ≤ a ^ n * ∑ i ∈ Finset.range (N + 1), f i := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Finset.sum_filter_of_ne (p := fun i => i ≤ N)]
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_filter] at hi
            exact Finset.mem_range.2 (Nat.lt_succ_of_le hi.2)
          · intro i _ _; exact hf0 i
        · intro i _ hne
          by_contra hle
          apply hne
          simp only [hf, Nat.choose_eq_zero_of_lt (lt_of_not_ge hle), Nat.cast_zero, zero_mul]
    _ = a ^ n * (1 - (1 - 1 / a) * ε) ^ N := by
        congr 1
        have : 1 - (1 - 1 / a) * ε = ε / a + (1 - ε) := by field_simp; ring
        rw [this, add_pow]
        apply Finset.sum_congr rfl
        intro i _; simp only [hf]; ring

theorem binomial_sum_le_exp_core (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (a : ℝ) (ha : a = 1 + 1 / Real.sqrt k)
    (εk : ℝ) (hε0 : 0 ≤ εk) (hε1 : εk ≤ 1) :
    (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        a ^ (k + d - 1) * (1 - (1 - 1 / a) * εk) ^ N) ∧
      (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        Real.exp (-(1 - a) * ((k + d - 1 : ℕ) : ℝ)) * Real.exp (-(1 - 1 / a) * εk * N)) := by
  have ha1 : 1 ≤ a := by rw [ha]; have := Real.sqrt_nonneg (k : ℝ); have : 0 ≤ 1 / Real.sqrt k := by positivity
                         linarith
  have hkd : k + d = (k + d - 1) + 1 := by omega
  have H := bin_sum_le_core N (k + d - 1) a εk ha1 hε0 hε1
  rw [← hkd] at H
  refine ⟨H, H.trans ?_⟩
  have ha0 : 0 < a := by linarith
  have hx0 : 0 ≤ 1 - 1 / a := by
    rw [sub_nonneg, div_le_one ha0]; exact ha1
  have hx1 : 1 - 1 / a ≤ 1 := by have : 0 ≤ 1 / a := by positivity
                                 linarith
  have hy0 : 0 ≤ 1 - (1 - 1 / a) * εk := by nlinarith
  apply mul_le_mul
  · calc a ^ (k + d - 1) ≤ (Real.exp (a - 1)) ^ (k + d - 1) := by
          apply pow_le_pow_left₀ ha0.le
          have := Real.add_one_le_exp (a - 1); linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  · calc (1 - (1 - 1 / a) * εk) ^ N ≤ (Real.exp (-((1 - 1 / a) * εk))) ^ N := by
          apply pow_le_pow_left₀ hy0
          have := Real.add_one_le_exp (-((1 - 1 / a) * εk)); linarith
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  · positivity
  · positivity

end ScenarioApproach.Removal

open ScenarioApproach.Removal


theorem solution (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (a : ℝ) (ha : a = 1 + 1 / Real.sqrt k)
    (εk : ℝ) (hε0 : 0 ≤ εk) (hε1 : εk ≤ 1) :
    (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        a ^ (k + d - 1) * (1 - (1 - 1 / a) * εk) ^ N) ∧
      (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        Real.exp (-(1 - a) * ((k + d - 1 : ℕ) : ℝ)) * Real.exp (-(1 - 1 / a) * εk * N)) := by
  exact binomial_sum_le_exp_core N k d hk hd a ha εk hε0 hε1
