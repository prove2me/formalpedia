-- Prove2me | solution 1 for StochSchedPrec.InForest.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:22:16.361743+00:00
-- url     : https://prove2.me/submissions/be772cc7-51e0-4c9a-a6f9-6396a5b18508

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_LP

set_option autoImplicit false
open StochSchedPrec.InForest

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (Δ : ℝ) (hΔ : 0 ≤ Δ) (μ : V → ℝ) (hμ : ∀ j, 0 < μ j)
    (C : V → ℝ) (hload : ∀ W : Finset V, f μ m Δ W ≤ ∑ j ∈ W, μ j * C j)
    (hlow : ∀ j, μ j ≤ C j)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsSortedBy L C) (j : V) :
    1 / (m : ℝ) * ∑ k ∈ Bset L j, μ k ≤ (1 + max 1 (((m : ℝ) - 1) / m * Δ)) * C j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set W := Bset L j with hW
  have hjW : j ∈ W := by
    rw [hW, Bset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, le_rfl⟩
  have hCk : ∀ k ∈ W, C k ≤ C j := by
    intro k hk
    rw [hW, Bset, Finset.mem_filter] at hk
    have := hL (L.symm k) (L.symm j) hk.2
    simpa using this
  set S := ∑ k ∈ W, μ k with hS
  set Q := ∑ k ∈ W, μ k ^ 2 with hQ
  have hSpos : 0 < S := Finset.sum_pos (fun k _ => hμ k) ⟨j, hjW⟩
  have hCj : 0 < C j := lt_of_lt_of_le (hμ j) (hlow j)
  have hQle : Q ≤ C j * S := by
    rw [hS, hQ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h1 : μ k ≤ C j := (hlow k).trans (hCk k hk)
    nlinarith [hμ k]
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsum : ∑ k ∈ W, μ k * C k ≤ C j * S := by
    rw [hS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have := hCk k hk
    nlinarith [hμ k]
  have hf := (hload W).trans hsum
  unfold f at hf
  rw [← hS, ← hQ] at hf
  set T := max 1 (((m : ℝ) - 1) / m * Δ) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT2 : ((m : ℝ) - 1) / m * Δ ≤ T := le_max_right _ _
  have hT3 : ((m : ℝ) - 1) * Δ ≤ m * T := by
    have : ((m : ℝ) - 1) * Δ = m * (((m : ℝ) - 1) / m * Δ) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hT2 hmR.le
  have hmain : S ≤ m * (1 + T) * C j := by
    have hf2 : S ^ 2 + Q - ((m : ℝ) - 1) * (Δ - 1) * Q ≤ 2 * m * (C j * S) := by
      have h3 : 1 / (2 * (m : ℝ)) * (S ^ 2 + Q) - ((m : ℝ) - 1) * (Δ - 1) / (2 * m) * Q
          = (S ^ 2 + Q - ((m : ℝ) - 1) * (Δ - 1) * Q) / (2 * m) := by field_simp
      rw [h3, div_le_iff₀ (by positivity)] at hf
      linarith
    by_cases hκ : ((m : ℝ) - 1) * (Δ - 1) - 1 ≤ 0
    · have h4 : S * S ≤ (2 * m * C j) * S := by nlinarith
      have h5 := le_of_mul_le_mul_right h4 hSpos
      nlinarith
    · push_neg at hκ
      have h4 : S * S ≤ (2 * m * C j + (((m : ℝ) - 1) * (Δ - 1) - 1) * C j) * S := by
        nlinarith
      have h5 := le_of_mul_le_mul_right h4 hSpos
      nlinarith
  rw [one_div, inv_mul_le_iff₀ hmR]
  nlinarith
