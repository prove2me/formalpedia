-- Prove2me | solution 1 for SuttonBartoRL.ImportanceSampling.weighted_average_incremental
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:09:28.391005+00:00
-- url     : https://prove2.me/submissions/f2e6b1e3-8822-4f4b-b711-cf3327c7b604

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_WeightedAverage

set_option autoImplicit false

namespace P603335db

open SuttonBartoRL.ImportanceSampling

lemma cumWeight_eq (W : ℕ → ℝ) (n : ℕ) :
    cumWeight W n = ∑ k ∈ Finset.Icc 1 n, W k := by
  induction n with
  | zero => simp [cumWeight]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    rfl

lemma cumWeight_pos (W : ℕ → ℝ) (hW : ∀ k, 1 ≤ k → 0 ≤ W k) (hW1 : 0 < W 1) :
    ∀ m, 1 ≤ m → 0 < cumWeight W m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [cumWeight, hW1]
    · show 0 < cumWeight W m + W (m + 1)
      have := ih h
      have := hW (m + 1) (by omega)
      linarith

lemma main (W G : ℕ → ℝ) (V₁ : ℝ) (hW : ∀ k, 1 ≤ k → 0 ≤ W k)
    (hW1 : 0 < W 1) : ∀ m, 1 ≤ m →
    incrementalEstimate W G V₁ (m + 1) =
      (∑ k ∈ Finset.Icc 1 m, W k * G k) / cumWeight W m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have hc : cumWeight W 1 = W 1 := by simp [cumWeight]
      show incrementalEstimate W G V₁ 1 +
          W 1 / cumWeight W 1 * (G 1 - incrementalEstimate W G V₁ 1) = _
      rw [hc]
      simp only [incrementalEstimate, Finset.Icc_self, Finset.sum_singleton]
      field_simp
      ring
    · have hpos := cumWeight_pos W hW hW1 m h
      have hpos' := cumWeight_pos W hW hW1 (m + 1) (by omega)
      have ih' := ih h
      show incrementalEstimate W G V₁ (m + 1) +
          W (m + 1) / cumWeight W (m + 1) * (G (m + 1) - incrementalEstimate W G V₁ (m + 1)) = _
      have hc : cumWeight W (m + 1) = cumWeight W m + W (m + 1) := rfl
      rw [ih', Finset.sum_Icc_succ_top (by omega)]
      rw [hc] at hpos' ⊢
      field_simp
      ring

end P603335db

open SuttonBartoRL.ImportanceSampling in
theorem solution (W G : ℕ → ℝ) (V₁ : ℝ) (hW : ∀ k, 1 ≤ k → 0 ≤ W k)
    (hW1 : 0 < W 1) (n : ℕ) (hn : 2 ≤ n) :
    incrementalEstimate W G V₁ n = weightedAverage W G n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [P603335db.main W G V₁ hW hW1 m (by omega), weightedAverage,
    P603335db.cumWeight_eq]
  simp
