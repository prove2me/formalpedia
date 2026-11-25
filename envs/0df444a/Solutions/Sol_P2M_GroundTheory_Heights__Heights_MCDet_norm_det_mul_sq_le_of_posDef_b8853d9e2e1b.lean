-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_of_posDef_b8853d9e2e1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:10:57.42905+00:00
-- url     : https://prove2.me/submissions/376c16b0-980e-4557-8ee3-3d7bff23b1c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
namespace GroundTheory.Heights₂.Heights.MCDet
theorem _root_.solution [DecidableEq m] {M : Matrix m m 𝕜} (hM : M.PosDef)
    (F W : Matrix m n 𝕜) :
    ‖(Wᴴ * F).det‖ ^ 2 ≤ RCLike.re (Wᴴ * M * W).det * RCLike.re (Fᴴ * M⁻¹ * F).det := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hL
  have hLdet : L.det ≠ 0 := by
    intro hl
    have := hM.det_pos.ne'
    rw [hL, det_mul, hl, mul_zero] at this
    exact this rfl
  have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr hLdet
  have hLHu : IsUnit Lᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hLdet)
  have h := norm_det_mul_sq_le ((Lᴴ)⁻¹ * F) (L * W)
  have e1 : (L * W)ᴴ * ((Lᴴ)⁻¹ * F) = Wᴴ * F := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ,
      Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul]
  have e2 : (L * W)ᴴ * (L * W) = Wᴴ * M * W := by
    rw [conjTranspose_mul, hL, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have e3 : ((Lᴴ)⁻¹ * F)ᴴ * ((Lᴴ)⁻¹ * F) = Fᴴ * M⁻¹ * F := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hL,
      Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc L⁻¹]
  rw [e1, e2, e3] at h
  exact h
end GroundTheory.Heights₂.Heights.MCDet
