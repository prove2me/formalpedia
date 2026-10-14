-- Prove2me | solution 1 for ScenarioApproach.Fast.fast_bound_le_of_N2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:05:49.412348+00:00
-- url     : https://prove2.me/submissions/d1cb9b44-64ed-4f62-8a07-327d9e4d45c7

import Mathlib



namespace ScenarioApproach.Fast

theorem fbn2_core (d N₁ N₂ : ℕ) (ε β : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN₂ : (1 / ε) * Real.log (1 / β) ≤ N₂) :
    (1 - ε) ^ N₂ *
        ∑ i ∈ Finset.range d, (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i) ≤ β := by
  set f : ℕ → ℝ := fun i => (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i) with hf
  have hfnn : ∀ i, 0 ≤ f i := fun i => by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hS1 : ∑ i ∈ Finset.range d, f i ≤ 1 := by
    rw [← Finset.sum_filter_of_ne (p := fun i => i ≤ N₁)]
    · calc ∑ i ∈ (Finset.range d).filter (fun i => i ≤ N₁), f i
          ≤ ∑ i ∈ Finset.range (N₁ + 1), f i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              simp only [Finset.mem_filter] at hx
              simp only [Finset.mem_range]; omega
            · intro i _ _; exact hfnn i
        _ = (ε + (1 - ε)) ^ N₁ := by
            rw [add_pow]; apply Finset.sum_congr rfl; intro i _; simp only [hf]; ring
        _ = 1 := by norm_num
    · intro x _ hx
      by_contra hc
      apply hx
      simp only [hf]
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hSnn : 0 ≤ ∑ i ∈ Finset.range d, f i := Finset.sum_nonneg fun i _ => hfnn i
  have hP : (1 - ε) ^ N₂ ≤ β := by
    have h1 : (1 - ε) ^ N₂ ≤ (Real.exp (-ε)) ^ N₂ :=
      pow_le_pow_left₀ (by linarith) (by
        have := Real.add_one_le_exp (-ε); linarith) _
    have h2 : (Real.exp (-ε)) ^ N₂ = Real.exp (N₂ * (-ε)) := (Real.exp_nat_mul _ _).symm
    have h3 : Real.log (1 / β) ≤ ε * N₂ := by
      have := mul_le_mul_of_nonneg_left hN₂ hε0.le
      rwa [← mul_assoc, mul_one_div_cancel hε0.ne', one_mul] at this
    have h4 : Real.exp (N₂ * (-ε)) ≤ β := by
      have hl : Real.log (1 / β) = - Real.log β := by
        rw [one_div, Real.log_inv]
      calc Real.exp (N₂ * (-ε)) ≤ Real.exp (Real.log β) := by
            apply Real.exp_le_exp.mpr; rw [hl] at h3; linarith
        _ = β := Real.exp_log hβ0
    linarith
  calc (1 - ε) ^ N₂ * ∑ i ∈ Finset.range d, f i ≤ β * 1 :=
        mul_le_mul hP hS1 hSnn hβ0.le
    _ = β := mul_one β

end ScenarioApproach.Fast

open ScenarioApproach.Fast


theorem solution (d N₁ N₂ : ℕ) (ε β : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN₂ : (1 / ε) * Real.log (1 / β) ≤ N₂) :
    (1 - ε) ^ N₂ *
        ∑ i ∈ Finset.range d, (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i) ≤ β := by
  exact fbn2_core d N₁ N₂ ε β hε0 hε1 hβ0 hβ1 hN₂
