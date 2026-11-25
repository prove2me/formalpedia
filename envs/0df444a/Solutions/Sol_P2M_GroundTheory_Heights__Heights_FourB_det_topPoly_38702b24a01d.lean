-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:42.695182+00:00
-- url     : https://prove2.me/submissions/ea31d7c0-3bfc-4b51-bf86-a7f11ae2da67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ}
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)
variable {L}
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly i hi L).det = 1 := by
  rw [det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly, colPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have h1 : Fin.castLE hi a ≠ Fin.castLE hi b := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi a) (Fin.castLE hi b) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly, colPoly, h1, h2]
end GroundTheory.Heights₂.Heights.FourB
