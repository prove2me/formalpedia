-- Prove2me | solution 1 for RegLearnGames.IndivRegret.oftrl_stability
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:22:00.286346+00:00
-- url     : https://prove2.me/submissions/9150822e-2bc1-4e72-863a-51ea585d70ca

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_IndivRegret_lemma_20

open Finset RegLearnGames.TotalRegret

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (u w : ℕ → Fin d → ℝ)
    (hu : ∀ t x, u t x ∈ Set.Icc (0 : ℝ) 1)
    (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η (fun T => u (T - 1)) u w) :
    ∀ t, RegLearnGames.TotalRegret.l1 (w t - w (t + 1)) ≤ 2 * η := by
  classical
  have hex (t : ℕ) : ∃ y ∈ stdSimplex ℝ (Fin d), ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ (∑ s ∈ Icc 1 t, u s) - 𝓡 v / η ≤
        y ⬝ᵥ (∑ s ∈ Icc 1 t, u s) - 𝓡 y / η := by
    have hc : Continuous (fun v : Fin d → ℝ => v ⬝ᵥ (∑ s ∈ Icc 1 t, u s)) := by
      fun_prop
    exact (isCompact_stdSimplex ℝ (Fin d)).exists_isMaxOn ⟨w 0, hw.1.1⟩
      (hc.continuousOn.sub (h𝓡.1.div_const η))
  choose g hg using hex
  have hleader : IsLeader 𝓡 η u g := hg
  have hs := RegLearnGames.IndivRegret.lemma_20 𝓡 η hη h𝓡
    (fun t => u (t - 1)) u w g hw hleader
  have hn : ∀ t, ‖u t‖ ≤ 1 := by
    intro t
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hu t x).1] using (hu t x).2
  have hd : ∀ s t, ‖u s - u t‖ ≤ 1 := by
    intro s t
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro x
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hu s x).1, (hu s x).2, (hu t x).1, (hu t x).2]
  intro t
  have htriangle : l1 (w t - w (t + 1)) ≤ l1 (w t - g t) + l1 (g t - w (t + 1)) := by
    simp only [l1, Pi.sub_apply, ← sum_add_distrib]
    exact sum_le_sum fun x _ => abs_sub_le (w t x) (g t x) (w (t + 1) x)
  have ha := (hs t).1.trans (mul_le_mul_of_nonneg_left (hd (t - 1) t) hη.le)
  have hb := (hs t).2.trans (mul_le_mul_of_nonneg_left (hn ((t + 1) - 1)) hη.le)
  linarith
