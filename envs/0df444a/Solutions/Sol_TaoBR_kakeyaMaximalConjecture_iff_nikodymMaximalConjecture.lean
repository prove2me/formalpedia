-- Prove2me | solution 1 for TaoBR.kakeyaMaximalConjecture_iff_nikodymMaximalConjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:00:25.49829+00:00
-- url     : https://prove2.me/submissions/16a327eb-b97a-4196-9a3f-078f3e20fb29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate

open MeasureTheory
open scoped ENNReal

namespace TaoBR

/-- `δ ↦ δ^a` is antitone in `a` on `(0, 1]`, so a bound with a smaller loss implies one with a
larger loss once `δ₀ ≤ 1`. -/
theorem ofReal_mul_rpow_le_of_le {C δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hab : b ≤ a) :
    ENNReal.ofReal (C * δ ^ a) ≤ ENNReal.ofReal (max C 0 * δ ^ b) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : δ ^ a ≤ δ ^ b := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hab
  have h2 : 0 ≤ δ ^ a := Real.rpow_nonneg hδ.le a
  calc C * δ ^ a ≤ max C 0 * δ ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
    _ ≤ max C 0 * δ ^ b := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

theorem kakeyaMaximalEstimate_mono {n : ℕ} {p α β : ℝ} (hαβ : α ≤ β)
    (h : KakeyaMaximalEstimate n p α) : KakeyaMaximalEstimate n p β := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h
  refine ⟨max C 0, min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ hδ' f hf => ?_⟩
  refine (hC δ hδ (lt_of_lt_of_le hδ' (min_le_left _ _)) f hf).trans ?_
  exact mul_le_mul_of_nonneg_right
    (ofReal_mul_rpow_le_of_le hδ ((lt_of_lt_of_le hδ' (min_le_right _ _)).le) (by linarith)) (by positivity)

theorem nikodymMaximalEstimate_mono {n : ℕ} {p α β : ℝ} (hαβ : α ≤ β)
    (h : NikodymMaximalEstimate n p α) : NikodymMaximalEstimate n p β := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h
  refine ⟨max C 0, min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ hδ' f hf => ?_⟩
  refine (hC δ hδ (lt_of_lt_of_le hδ' (min_le_left _ _)) f hf).trans ?_
  exact mul_le_mul_of_nonneg_right
    (ofReal_mul_rpow_le_of_le hδ ((lt_of_lt_of_le hδ' (min_le_right _ _)).le) (by linarith)) (by positivity)

theorem kakeyaMaximalConjecture_iff_nikodymMaximalConjecture_dev (n : ℕ) (hn : 2 ≤ n) :
    KakeyaMaximalConjecture n ↔ NikodymMaximalConjecture n := by
  constructor
  · intro hK p hp1 hpn α hα
    have hp0 : 0 < p := by linarith
    have hc : 0 < ((n : ℝ) + 1) / (2 * p) := by positivity
    set α' := min α (((n : ℝ) + 1) / (2 * p)) with hα'
    have hα'0 : 0 < α' := lt_min hα hc
    have hα'lt : α' < ((n : ℝ) + 1) / p := by
      have : ((n : ℝ) + 1) / (2 * p) < ((n : ℝ) + 1) / p := by
        rw [div_lt_div_iff₀ (by positivity) hp0]; nlinarith
      exact lt_of_le_of_lt (min_le_right _ _) this
    have := (nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
      n hn p hp1 hpn α' hα'0.le hα'lt).1 (hK p hp1 hpn α' hα'0)
    exact nikodymMaximalEstimate_mono (min_le_left _ _) this
  · intro hN p hp1 hpn α hα
    have hp0 : 0 < p := by linarith
    have hc : 0 < ((n : ℝ) + 1) / (2 * p) := by positivity
    set α' := min (α / 2) (((n : ℝ) + 1) / (2 * p)) with hα'
    have hα'0 : 0 < α' := lt_min (by linarith) hc
    have hα'lt : α' < ((n : ℝ) + 1) / p := by
      have : ((n : ℝ) + 1) / (2 * p) < ((n : ℝ) + 1) / p := by
        rw [div_lt_div_iff₀ (by positivity) hp0]; nlinarith
      exact lt_of_le_of_lt (min_le_right _ _) this
    have := (nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
      n hn p hp1 hpn α' hα'0.le hα'lt).2 (hN p hp1 hpn α' hα'0)
    refine kakeyaMaximalEstimate_mono ?_ this
    have := min_le_left (α / 2) (((n : ℝ) + 1) / (2 * p))
    linarith

end TaoBR

open TaoBR in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    KakeyaMaximalConjecture n ↔ NikodymMaximalConjecture n :=
  kakeyaMaximalConjecture_iff_nikodymMaximalConjecture_dev n hn
