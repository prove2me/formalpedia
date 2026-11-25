-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_norm_det_sigTop_d1ab7a11e30b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:57.465265+00:00
-- url     : https://prove2.me/submissions/d3a158ad-b2c1-4b7e-ac24-070de8936a1f

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
theorem _root_.solution : ‖(sigTop p i hi).det‖ = 1 := by
  rw [sigTop, det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sigSign
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FourB
