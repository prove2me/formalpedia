-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_colPoly_eval_e4846f8558e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:53.953464+00:00
-- url     : https://prove2.me/submissions/cd6c3ce3-3390-4977-95ff-d5957b513440

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
theorem _root_.solution (u : LowerPair N → ℂ) (t : ℝ) :
    (colPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id (Fin.castLE hi) := by
  refine Matrix.ext fun c b => ?_
  by_cases h : Fin.castLE hi b < c
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h, Complex.real_smul] <;> split_ifs <;>
      simp [mul_comm]
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h] <;> split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FourB
