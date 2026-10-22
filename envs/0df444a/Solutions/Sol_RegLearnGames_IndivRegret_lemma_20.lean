-- Prove2me | solution 1 for RegLearnGames.IndivRegret.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:21:15.03055+00:00
-- url     : https://prove2.me/submissions/984c4395-7c8e-4032-a67c-c449c7233834

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Theorems.Thm_RegLearnGames_TotalRegret_lemma_20

open Finset RegLearnGames.TotalRegret

theorem solution {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (M u w g : ℕ → Fin d → ℝ)
    (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η M u w) (hg : RegLearnGames.TotalRegret.IsLeader 𝓡 η u g) :
    ∀ t, RegLearnGames.TotalRegret.l1 (w t - g t) ≤ η * ‖M t - u t‖ ∧ RegLearnGames.TotalRegret.l1 (g t - w (t + 1)) ≤ η * ‖M (t + 1)‖ := by
  exact RegLearnGames.TotalRegret.lemma_20 𝓡 η hη h𝓡 M u w g hw hg
