-- Prove2me | solution 1 for RevenueOrdered.PurchaseRatio.sum_profile_ratio_le_one_add_log
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:11:54.288513+00:00
-- url     : https://prove2.me/submissions/d76f6fda-042e-4bf1-92bc-ef20d0c539b4

import Mathlib

set_option autoImplicit false

lemma rops_3f1d20f0_pos (N : ℕ → ℝ) (ℓ : ℕ)
    (hanti : ∀ i, 1 ≤ i → i < ℓ → N (i + 1) ≤ N i) :
    ∀ d i, i + d = ℓ → 1 ≤ i → N ℓ ≤ N i := by
  intro d
  induction d with
  | zero => intro i h _; simp at h; subst h; exact le_rfl
  | succ d ih =>
    intro i h hi
    have h1 := ih (i + 1) (by omega) (by omega)
    have h2 := hanti i hi (by omega)
    linarith

lemma rops_3f1d20f0_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b) / a ≤ Real.log a - Real.log b := by
  have hx : 0 < b / a := div_pos hb ha
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div hb.ne' ha.ne'] at h
  have : (a - b) / a = 1 - b / a := by field_simp
  rw [this]; linarith

theorem solution (N : ℕ → ℝ) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ)
    (hanti : ∀ i, 1 ≤ i → i < ℓ → N (i + 1) ≤ N i) (hℓpos : 0 < N ℓ) (hsucc : N (ℓ + 1) = 0) :
    ∑ i ∈ Finset.Icc 1 ℓ, (N i - N (i + 1)) / N i ≤ 1 + Real.log (N 1 / N ℓ) := by
  have hpos : ∀ i, 1 ≤ i → i ≤ ℓ → 0 < N i := by
    intro i hi hil
    have := rops_3f1d20f0_pos N ℓ hanti (ℓ - i) i (by omega) hi
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have key : ∀ k, k ≤ m →
      ∑ i ∈ Finset.Icc 1 k, (N i - N (i + 1)) / N i ≤ Real.log (N 1) - Real.log (N (k + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih (by omega)
      have h2 := rops_3f1d20f0_step (N (k + 1)) (N (k + 1 + 1))
        (hpos (k + 1) (by omega) (by omega)) (hpos (k + 1 + 1) (by omega) (by omega))
      linarith
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hk := key m le_rfl
  rw [hsucc, sub_zero, div_self hℓpos.ne',
    Real.log_div (hpos 1 (by omega) (by omega)).ne' hℓpos.ne']
  linarith
