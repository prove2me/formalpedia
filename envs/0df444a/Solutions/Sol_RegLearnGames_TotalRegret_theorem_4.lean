-- Prove2me | solution 1 for RegLearnGames.TotalRegret.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:18:00.099236+00:00
-- url     : https://prove2.me/submissions/ddfe4f67-65b4-474a-91b1-5709f3b56a14

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_TotalRegret_theorem_4_variation_bound

open Finset RegLearnGames.TotalRegret

theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : ∀ t i, w t i ∈ stdSimplex ℝ (Fin d))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hβγn : β * ((n : ℝ) - 1) ^ 2 ≤ γ) (T : ℕ)
    (hRVU : ∀ i, ∀ v ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (v - w t i) ⬝ᵥ utilVec u (w t) i ≤
        α + β * ∑ t ∈ Finset.Icc 1 T, ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2
          - γ * ∑ t ∈ Finset.Icc 1 T, l1 (w t i - w (t - 1) i) ^ 2)
    (wstar : Fin n → Fin d → ℝ) (hwstar : ∀ i, wstar i ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ∑ t ∈ Finset.Icc 1 T, (wstar i - w t i) ⬝ᵥ utilVec u (w t) i ≤ α * n := by
  classical
  let A : ℝ := ∑ i, ∑ t ∈ Icc 1 T,
    ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2
  let D : ℝ := ∑ i, ∑ t ∈ Icc 1 T, l1 (w t i - w (t - 1) i) ^ 2
  have hD : 0 ≤ D := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hvar : A ≤ ((n : ℝ) - 1) ^ 2 * D := by
    calc
      A = ∑ t ∈ Icc 1 T, ∑ i,
          ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2 := by
        dsimp [A]; rw [sum_comm]
      _ ≤ ∑ t ∈ Icc 1 T, ((n : ℝ) - 1) ^ 2 *
          ∑ i, l1 (w t i - w (t - 1) i) ^ 2 := by
        refine sum_le_sum fun t _ => ?_
        have h := theorem_4_variation_bound u hu (w t) (w (t - 1)) (hw t) (hw (t - 1))
        exact h.1.trans_eq h.2
      _ = ((n : ℝ) - 1) ^ 2 * D := by
        rw [← mul_sum, sum_comm]
  have hcancel : β * A ≤ γ * D := by
    calc
      β * A ≤ β * (((n : ℝ) - 1) ^ 2 * D) :=
        mul_le_mul_of_nonneg_left hvar hβ.le
      _ = (β * ((n : ℝ) - 1) ^ 2) * D := by ring
      _ ≤ γ * D := mul_le_mul_of_nonneg_right hβγn hD
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    hRVU i (wstar i) (hwstar i)
  have hrhs : (∑ i, (α + β * ∑ t ∈ Icc 1 T,
      ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2
      - γ * ∑ t ∈ Icc 1 T, l1 (w t i - w (t - 1) i) ^ 2)) =
        α * n + β * A - γ * D := by
    simp only [A, D, sum_sub_distrib, sum_add_distrib, ← mul_sum,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hrhs] at hsum
  linarith
