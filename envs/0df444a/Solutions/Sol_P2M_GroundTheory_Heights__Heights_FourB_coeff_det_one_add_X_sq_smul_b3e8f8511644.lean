-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_coeff_det_one_add_X_sq_smul_b3e8f8511644
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:35.992387+00:00
-- url     : https://prove2.me/submissions/3d16b942-480d-499a-a27a-6735fa497ed6

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ[X]) :
    (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 0 = 1 ∧ (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 1 = 0 ∧
      (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 2 = K.trace.coeff 0 := by
  rw [det_one_add_smul]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_one, ← pow_mul, coeff_mul_X_pow']
end GroundTheory.Heights₂.Heights.FourB
