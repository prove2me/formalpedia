-- Prove2me | solution 1 for TarchaBraids.thm_3_15_right_interp_u_boundaries_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T12:08:44.706221+00:00
-- url     : https://prove2.me/submissions/7b399555-aec5-4d33-be16-7fce9017bbb0

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_config_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma rightInterp_zero_u_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (q : unitInterval) :
    configProj n (rightOuterInterpConfig i j hji 0 q) =
      configProj n (rightBraidConfig n i j (q : ℝ)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  simp [rightOuterInterpConfig, rightOuterInterpFun, braidInterp, rightBraidConfig]

lemma rightInterp_one_u_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (hi2 : (i : ℕ) + 2 < n)
    (q : unitInterval) :
    configProj n (rightOuterInterpConfig i j hji 1 q) =
      configProj n (outerRotateConfig i hi2 (q : ℝ)) := by
  apply congrArg (configProj n)
  apply Subtype.ext
  funext k
  simp [rightOuterInterpConfig, rightOuterInterpFun, braidInterp, outerRotateConfig]

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : unitInterval,
        configProj n (rightOuterInterpConfig i j hji 0 q) =
          configProj n (rightBraidConfig n i j (q : ℝ))) ∧
      (∀ (hi2 : (i : ℕ) + 2 < n) (q : unitInterval),
        configProj n (rightOuterInterpConfig i j hji 1 q) =
          configProj n (outerRotateConfig i hi2 (q : ℝ))) := by
  intro n i j hji
  exact ⟨rightInterp_zero_u_v1 i j hji,
    fun hi2 => rightInterp_one_u_v1 i j hji hi2⟩
