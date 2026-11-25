-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_lowerMatrix_strict_2110b5ac3e82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:54.93189+00:00
-- url     : https://prove2.me/submissions/41b13388-0f76-4c5e-a7b4-951bd9212898

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
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
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (u : LowerPair N → ℂ) :
    ∀ a b : Fin N, ¬ b < a → lowerMatrix u a b = 0 := by
  intro a b h
  simp [lowerMatrix, h]
end GroundTheory.Heights₂.Heights.FourB
