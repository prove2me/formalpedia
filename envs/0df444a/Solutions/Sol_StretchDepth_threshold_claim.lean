-- Prove2me | solution 1 for StretchDepth.threshold_claim
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:30:17.922675+00:00
-- url     : https://prove2.me/submissions/3634b106-20d2-4da7-9805-b694c7ae750a

import Mathlib
import Definitions.Def_StretchDepth_crit

open StretchDepth

theorem solution (N d : ℕ) (hd : 1 ≤ d) (ℓ τ : ℝ)
    (hℓ : 0 < ℓ) (hℓN : ℓ < N) (hτ : 0 ≤ τ)
    (t : ℕ → ℕ) (ht0 : t 0 = 0) (htd : τ ≤ t d) :
    ∃ j, 1 ≤ j ∧ j ≤ d ∧ alpha N ℓ d * τ ≤ ℓ * t j - (N : ℝ) * t (j - 1) := by
  by_contra! h
  let r : ℝ := (N : ℝ) / ℓ
  let D : ℝ := r ^ d - 1
  have hr : 1 < r := (lt_div_iff₀ hℓ).2 (by simpa using hℓN)
  have hr0 : 0 ≤ r := by linarith
  have hD : 0 < D := sub_pos.mpr (one_lt_pow₀ hr (by omega))
  have hrel : (N : ℝ) = r * ℓ := by
    dsimp [r]
    field_simp
  have ha : alpha N ℓ d * D = ℓ * (r - 1) := by
    change (((N : ℝ) - ℓ) / D) * D = ℓ * (r - 1)
    rw [div_mul_cancel₀ _ hD.ne', hrel]
    ring
  have step (i : ℕ) (hi : i < d)
      (hp : D * (t i : ℝ) ≤ τ * (r ^ i - 1)) :
      D * (t (i + 1) : ℝ) < τ * (r ^ (i + 1) - 1) := by
    have hx := h (i + 1) (by omega) (by omega)
    have hh := mul_lt_mul_of_pos_right hx hD
    have hy := mul_le_mul_of_nonneg_left hp hr0
    have hh' : D * (t (i + 1) : ℝ) < r * (D * (t i : ℝ)) + (r - 1) * τ := by
      have hh'' : ℓ * (D * (t (i + 1) : ℝ)) <
          ℓ * (r * (D * (t i : ℝ)) + (r - 1) * τ) := by
        simp only [Nat.add_sub_cancel] at hh
        rw [hrel] at hh
        nlinarith only [hh, congrArg (fun x : ℝ => x * τ) ha]
      exact lt_of_mul_lt_mul_left hh'' hℓ.le
    rw [pow_succ]
    nlinarith only [hh', hy]
  have aux (i : ℕ) (hi : i ≤ d) : D * (t i : ℝ) ≤ τ * (r ^ i - 1) := by
    induction i with
    | zero => simp [ht0]
    | succ i ih => exact (step i (by omega) (ih (by omega))).le
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hf := step i (by omega) (aux i (by omega))
  have hf' : D * (t (i + 1) : ℝ) < D * τ := by
    simpa only [D, mul_comm] using hf
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left htd hD.le)) hf'
