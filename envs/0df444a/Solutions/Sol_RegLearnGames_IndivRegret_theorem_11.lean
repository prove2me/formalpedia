-- Prove2me | solution 1 for RegLearnGames.IndivRegret.theorem_11
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:22:42.904693+00:00
-- url     : https://prove2.me/submissions/9acecd62-20a1-4663-b568-24604ad8dac8

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_IndivRegret_theorem_11_variation_bound

open Finset RegLearnGames.TotalRegret

theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : ∀ t i, w t i ∈ stdSimplex ℝ (Fin d))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) (T : ℕ)
    (hRVU : ∀ i, ∀ v ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (v - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * ∑ t ∈ Finset.Icc 1 T, ‖RegLearnGames.TotalRegret.utilVec u (w t) i - RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i‖ ^ 2
          - γ * ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t i - w (t - 1) i) ^ 2)
    (κ : ℝ) (hκ : ∀ i, ∀ t < T, RegLearnGames.TotalRegret.l1 (w t i - w (t + 1) i) ≤ κ) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * κ ^ 2 * ((n : ℝ) - 1) ^ 2 * T := by
  classical
  intro i wstar hwstar
  have hpoint : ∀ t ∈ Icc 1 T,
      ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2 ≤
        ((n : ℝ) - 1) ^ 2 * κ ^ 2 := by
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
    have htT : t ≤ T := (mem_Icc.mp ht).2
    have hm : t - 1 < T := by omega
    have heq : t - 1 + 1 = t := by omega
    have hdist : ∀ j, l1 (w t j - w (t - 1) j) ≤ κ := by
      intro j
      have h := hκ j (t - 1) hm
      rw [heq] at h
      simpa only [l1, Pi.sub_apply, abs_sub_comm] using h
    have h := RegLearnGames.IndivRegret.theorem_11_variation_bound u hu
      (w t) (w (t - 1)) (hw t) (hw (t - 1)) κ hdist i
    exact h.1.trans h.2
  have hsum : (∑ t ∈ Icc 1 T,
      ‖utilVec u (w t) i - utilVec u (w (t - 1)) i‖ ^ 2) ≤
        (T : ℝ) * (((n : ℝ) - 1) ^ 2 * κ ^ 2) := by
    calc
      _ ≤ ∑ t ∈ Icc 1 T, ((n : ℝ) - 1) ^ 2 * κ ^ 2 := sum_le_sum hpoint
      _ = _ := by simp
  have hmul := mul_le_mul_of_nonneg_left hsum hβ.le
  have hnonneg : 0 ≤ γ * ∑ t ∈ Icc 1 T, l1 (w t i - w (t - 1) i) ^ 2 :=
    mul_nonneg hγ (sum_nonneg fun _ _ => sq_nonneg _)
  have hr := hRVU i wstar hwstar
  nlinarith
