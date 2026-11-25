-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_norm_det_mul_sq_le_83a21f1546d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:27.570014+00:00
-- url     : https://prove2.me/submissions/73d7e293-9a79-4b48-8476-3537ef80c90d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455

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
theorem _root_.solution (A B : Matrix m n 𝕜) :
    ‖(Bᴴ * A).det‖ ^ 2 ≤ RCLike.re (Bᴴ * B).det * RCLike.re (Aᴴ * A).det := by
  have hG := posSemidef_conjTranspose_mul_self A
  have hBB := posSemidef_conjTranspose_mul_self B
  by_cases h0 : (Aᴴ * A).det = 0
  · obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hAx : A *ᵥ x = 0 := by
      have h := congrArg (fun v => star x ⬝ᵥ v) hx
      simp only [dotProduct_zero] at h
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose] at h
      simp only [star_star] at h
      exact dotProduct_star_self_eq_zero.mp h
    have hC : (Bᴴ * A).det = 0 :=
      exists_mulVec_eq_zero_iff.mp ⟨x, hx0, by rw [← mulVec_mulVec, hAx, mulVec_zero]⟩
    rw [hC, h0, norm_zero, map_zero]
    simp
  · have hGpd : (Aᴴ * A).PosDef := hG.posDef_iff_det_ne_zero.mpr h0
    set G := Aᴴ * A with hGdef
    set C := Bᴴ * A with hCdef
    have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr h0
    have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hGiH : (G⁻¹)ᴴ = G⁻¹ := by
      rw [conjTranspose_nonsing_inv, hGpd.isHermitian.eq]
    have hCH : Cᴴ = Aᴴ * B := by
      rw [hCdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set E := B - A * (G⁻¹ * Cᴴ) with hEdef
    have hcancel : ∀ Z : Matrix n n 𝕜, G⁻¹ * (Aᴴ * (A * Z)) = Z := by
      intro Z
      rw [← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← hGdef, hGiG, Matrix.one_mul]
    have hEE : Bᴴ * B = C * G⁻¹ * Cᴴ + Eᴴ * E := by
      rw [hEdef, hCH]
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hGiH]
      rw [hCdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel]
      abel
    have hPSD1 : (C * G⁻¹ * Cᴴ).PosSemidef := hGpd.inv.posSemidef.mul_mul_conjTranspose_same C
    have hPSD2 : (Eᴴ * E).PosSemidef := posSemidef_conjTranspose_mul_self E
    have hle := re_det_le_re_det_add hPSD1 hPSD2
    rw [← hEE] at hle
    have hg := re_det_pos hGpd
    have hdetC : (C * G⁻¹ * Cᴴ).det = ((‖C.det‖ ^ 2 * (RCLike.re G.det)⁻¹ : ℝ) : 𝕜) := by
      rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv',
        det_eq_ofReal_re hG, mul_comm (C.det), mul_assoc, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
    rw [hdetC, RCLike.ofReal_re] at hle
    rw [← div_eq_mul_inv, div_le_iff₀ hg] at hle
    exact hle
end GroundTheory.Heights₂.Heights.MCDet
