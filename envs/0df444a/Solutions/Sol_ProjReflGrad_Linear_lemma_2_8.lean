-- Prove2me | solution 1 for ProjReflGrad.Linear.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:30:29.41663+00:00
-- url     : https://prove2.me/submissions/6e7f905b-2b97-4a55-b463-6aa26ee6b277

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem solution (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (α0 β : ℝ)
    (hα0 : 0 < α0 ∧ α0 < 1) (hβ : 0 < β ∧ β < 1)
    (h21 : ∀ α : ℝ, 0 < α → α < α0 → ∀ n : ℕ, 1 ≤ n →
      a (n + 1) + b (n + 1) ≤ (1 - 2 * α) * a n + α * a (n - 1) + β * b n) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ n : ℕ, 0 < n → a n ≤ γ ^ n * M := by
  obtain ⟨hα00, hα01⟩ := hα0
  obtain ⟨hβ0, hβ1⟩ := hβ
  set α : ℝ := min (α0 / 2) (1 / 4) with hαdef
  have hα1 : 0 < α := lt_min (by linarith) (by norm_num)
  have hα2 : α < α0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hα3 : α ≤ 1 / 4 := min_le_right _ _
  set δ : ℝ := 3 * α / 2 with hδ
  set γ : ℝ := max (1 - α / 2) β with hγ
  have hγ1 : 1 - α / 2 ≤ γ := le_max_left _ _
  have hγ2 : β ≤ γ := le_max_right _ _
  have hγlt : γ < 1 := max_lt (by linarith) hβ1
  have hγpos : 0 < γ := lt_of_lt_of_le (by linarith) hγ1
  set V : ℕ → ℝ := fun n => a (n + 1) + δ * a n + b (n + 1) with hV
  have hVstep : ∀ n, V (n + 1) ≤ γ * V n := by
    intro n
    have h := h21 α hα1 hα2 (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have e1 : 0 ≤ a (n + 1) * (γ - (1 - 2 * α + δ)) := mul_nonneg (ha _) (by rw [hδ]; linarith)
    have e2 : 0 ≤ a n * (γ * δ - α) := mul_nonneg (ha _) (by rw [hδ]; nlinarith)
    have e3 : 0 ≤ b (n + 1) * (γ - β) := mul_nonneg (hb _) (by linarith)
    simp only [hV]
    nlinarith
  have hVpow : ∀ n, V n ≤ γ ^ n * V 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc V (k + 1) ≤ γ * V k := hVstep k
        _ ≤ γ * (γ ^ k * V 0) := mul_le_mul_of_nonneg_left ih hγpos.le
        _ = γ ^ (k + 1) * V 0 := by ring
  have hV0 : 0 ≤ V 0 := by
    simp only [hV]
    have := ha 1; have := ha 0; have := hb 1
    have : 0 ≤ δ := by rw [hδ]; linarith
    nlinarith [mul_nonneg this (ha 0)]
  refine ⟨γ, V 0 / γ + 1, hγpos, hγlt, by positivity, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : a (k + 1) ≤ V k := by
    simp only [hV]
    have : 0 ≤ δ * a k := mul_nonneg (by rw [hδ]; linarith) (ha k)
    have := hb (k + 1)
    linarith
  have h2 : γ ^ k * V 0 ≤ γ ^ (k + 1) * (V 0 / γ + 1) := by
    have hp : 0 < γ ^ k := pow_pos hγpos k
    have : γ ^ (k + 1) * (V 0 / γ + 1) = γ ^ k * V 0 + γ ^ (k + 1) := by
      field_simp
      ring
    rw [this]
    have := pow_pos hγpos (k + 1)
    linarith
  exact le_trans h1 (le_trans (hVpow k) h2)
