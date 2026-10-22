-- Prove2me | solution 1 for RegLearnGames.IndivRegret.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:21:40.444645+00:00
-- url     : https://prove2.me/submissions/f916f381-df3f-46b5-b715-89dba667800d

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_TotalRegret_proposition_7

open Finset RegLearnGames.TotalRegret

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (R : ℝ)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - (1 / (4 * η)) * ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t - w (t - 1)) ^ 2 := by
  exact RegLearnGames.TotalRegret.proposition_7 𝓡 η R hη h𝓡 hR u w hw T wstar hwstar
