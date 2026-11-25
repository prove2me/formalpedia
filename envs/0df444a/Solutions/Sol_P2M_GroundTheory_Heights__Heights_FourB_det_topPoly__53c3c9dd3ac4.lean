-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_det_topPoly__53c3c9dd3ac4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:45.418399+00:00
-- url     : https://prove2.me/submissions/ab063ca1-48fb-4cae-9e24-78fbeb82f78e

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
theorem _root_.solution (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly' i hi L).det = 1 := by
  rw [det_of_isUpperTriangular ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly', rowPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : b < a := by simpa using hab
    have h1 : Fin.castLE hi b ≠ Fin.castLE hi a := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi b) (Fin.castLE hi a) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly', rowPoly, h1, h2]
end GroundTheory.Heights₂.Heights.FourB
