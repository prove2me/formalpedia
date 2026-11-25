-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_det_gram_d092f848ed8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:58.546783+00:00
-- url     : https://prove2.me/submissions/03ff40f7-7e67-4aa8-b099-b0fa31e9bfd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_gram_eq_801d9bae3823
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_det_topPoly__53c3c9dd3ac4
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
theorem _root_.solution (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) :
    (rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L).det =
      C (sigTop p i hi).det * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L).det := by
  have hSS : (sigTop p i hi).map C * (sigTop p i hi).map C = 1 := by
    rw [← Matrix.map_mul, sigTop_mul_self]; simp
  have hK : topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L =
      (tailForm p i hi L).map C := by
    calc topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L
        = (topPoly' i hi L * ((sigTop p i hi).map C * (sigTop p i hi).map C) *
            (topPoly' i hi L).adjugate) * (tailForm p i hi L).map C *
            ((topPoly i hi L).adjugate * topPoly i hi L) := by
          simp only [kerPoly, Matrix.mul_assoc]
      _ = (tailForm p i hi L).map C := by
          rw [hSS, Matrix.mul_one, Matrix.mul_adjugate, Matrix.adjugate_mul, det_topPoly i hi hL,
            det_topPoly' i hi hL, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hfac : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
      topPoly' i hi L * (sigTop p i hi).map C * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L) *
        topPoly i hi L := by
    rw [gram_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, hK]
  rw [hfac, det_mul, det_mul, det_mul, det_topPoly i hi hL, det_topPoly' i hi hL, one_mul,
    mul_one]
  rw [show ((sigTop p i hi).map C).det = C (sigTop p i hi).det from
    ((C : ℂ →+* ℂ[X]).map_det _).symm]
end GroundTheory.Heights₂.Heights.FourB
