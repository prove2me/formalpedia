-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:33.861843+00:00
-- url     : https://prove2.me/submissions/46c2f550-73f6-4574-8406-0e263b74f1d4

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
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (p : ℕ) :
    signatureForm N p = diagonal fun a => ((sigSign p a : ℝ) : ℂ) := by
  unfold signatureForm
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FourB
