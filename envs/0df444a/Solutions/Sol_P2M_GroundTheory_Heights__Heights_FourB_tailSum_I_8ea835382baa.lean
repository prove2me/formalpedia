-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_tailSum_I_8ea835382baa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:36.830317+00:00
-- url     : https://prove2.me/submissions/bc81182c-6fe8-461b-8fe9-a8979cfb5938

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
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
open ReciprocityTheory.AnForm
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {N : ℕ} (p i : ℕ) (u : LowerPair N → ℂ) :
    tailSum p i (lowerMatrix (Complex.I • u)) = tailSum p i (lowerMatrix u) := by
  have : ∀ c b, ‖lowerMatrix (Complex.I • u) c b‖ = ‖lowerMatrix u c b‖ := by
    intro c b
    simp only [lowerMatrix, Matrix.of_apply]
    split_ifs <;> simp
  simp only [tailSum, this]
end GroundTheory.Heights₂.Heights.FourB
