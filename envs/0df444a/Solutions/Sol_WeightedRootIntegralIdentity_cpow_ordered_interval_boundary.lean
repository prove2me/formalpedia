-- Prove2me | solution 1 for WeightedRootIntegralIdentity.cpow_ordered_interval_boundary
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T15:20:07.436915+00:00
-- url     : https://prove2.me/submissions/02ccbbf3-9c1d-428e-a7fd-f2155dc0b20c

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
open scoped BigOperators

theorem solution
    (n k : ℕ) (a w : ℕ → ℝ)
    (hk : k < n - 1)
    (hmono : ∀ i j, i < j → j < n → a i ≤ a j)
    (x : ℝ) (hxlo : a k < x) (hxhi : x < a (k + 1)) :
    (∏ i ∈ Finset.range n, (((a i - x : ℝ) : ℂ) ^ (w i : ℂ))) =
      ((∏ i ∈ Finset.range n, Real.rpow |a i - x| (w i) : ℝ) : ℂ) *
        Complex.exp
          ((((Real.pi * (∑ i ∈ Finset.range (k + 1), w i) : ℝ) : ℝ) : ℂ) *
            Complex.I) := by
  have hkn : k + 1 < n := by omega
  have hlt (i : ℕ) (hi : i < n) : a i - x < 0 ↔ i < k + 1 := by
    constructor
    · intro hix
      by_contra hik
      have hki : k + 1 ≤ i := by omega
      by_cases heq : i = k + 1
      · subst i
        linarith
      · have hle : a (k + 1) ≤ a i := hmono (k + 1) i (by omega) hi
        linarith
    · intro hik
      have hikle : i ≤ k := by omega
      by_cases heq : i = k
      · subst i
        linarith
      · have hle : a i ≤ a k := hmono i k (by omega) (by omega)
        linarith
  have hzero : ∀ i ∈ Finset.range n, a i - x ≠ 0 := by
    intro i hi
    have hiN : i < n := Finset.mem_range.mp hi
    by_cases hik : i < k + 1
    · have hneg := (hlt i hiN).2 hik
      linarith
    · have hki : k + 1 ≤ i := by omega
      by_cases heq : i = k + 1
      · subst i
        linarith
      · have hle : a (k + 1) ≤ a i := hmono (k + 1) i (by omega) hiN
        linarith
  have hfilter :
      (Finset.range n).filter (fun i => a i - x < 0) = Finset.range (k + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hneg⟩
      exact (hlt i hi).1 hneg
    · intro hik
      have hi : i < n := lt_trans hik hkn
      exact ⟨hi, (hlt i hi).2 hik⟩
  have h := WeightedRootIntegralIdentity.cpow_finset_boundary_product
    (Finset.range n) (fun i => a i - x) w hzero
  rw [hfilter] at h
  exact h
