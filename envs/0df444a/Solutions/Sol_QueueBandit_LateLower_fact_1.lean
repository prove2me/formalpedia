-- Prove2me | solution 1 for QueueBandit.LateLower.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:40:33.005035+00:00
-- url     : https://prove2.me/submissions/0e89d5ba-61eb-494a-b8f4-c814402b19c6

import Mathlib

set_option autoImplicit false

open Finset Filter

theorem solution (a : ℕ → ℝ) (C : ℝ) (hC : 0 < C) (N₀ : ℕ)
    (hsum : ∀ n : ℕ, N₀ ≤ n → C * Real.log n ≤ ∑ m ∈ Icc 1 n, a m) :
    ∃ᶠ n : ℕ in atTop, C / (2 * (n : ℝ)) ≤ a n := by
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hcon
  set N₁ := max (max N₀ N₂) 1 with hN₁
  have h1 : ∀ n, N₁ ≤ n → a n < C / (2 * (n : ℝ)) := fun n hn =>
    not_le.1 (hN₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn))
  set S := ∑ m ∈ Icc 1 N₁, a m with hS
  have key : ∀ n, N₁ ≤ n → ∑ m ∈ Icc 1 n, a m ≤ S + C / 2 * (harmonic n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      have : (0 : ℝ) ≤ (harmonic N₁ : ℝ) := by
        have := harmonic_pos (n := N₁) (by omega)
        exact_mod_cast this.le
      nlinarith
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), harmonic_succ]
      have h2 := h1 (n + 1) (by omega)
      push_cast at h2 ⊢
      have : C / (2 * ((n : ℝ) + 1)) = C / 2 * ((n : ℝ) + 1)⁻¹ := by
        field_simp
      rw [this] at h2
      nlinarith
  set K : ℝ := 2 * S / C + 1 with hK
  have ev1 : ∀ᶠ n : ℕ in atTop, K < Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop K)
  have ev2 : ∀ᶠ n : ℕ in atTop, max N₁ N₀ ≤ n := eventually_ge_atTop _
  obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn2
  have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn2
  have h3 := hsum n hnN₀
  have h4 := key n hnN₁
  have h5 : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have h6 : C * Real.log n ≤ S + C / 2 * (1 + Real.log n) := by
    have : C / 2 * (harmonic n : ℝ) ≤ C / 2 * (1 + Real.log n) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  have h7 : K * C < Real.log n * C := mul_lt_mul_of_pos_right hn1 hC
  have h8 : K * C = 2 * S + C := by
    rw [hK]; field_simp
  nlinarith
