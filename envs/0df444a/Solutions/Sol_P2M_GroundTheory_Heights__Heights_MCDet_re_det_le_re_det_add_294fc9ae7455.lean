-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:08.073857+00:00
-- url     : https://prove2.me/submissions/2ac76596-a837-44c6-82ed-b47e94f51288

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_nonneg_2ff552c1453c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_one_le_re_det_one_add_4908d4f28098

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
theorem _root_.solution {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by
  by_cases h0 : A.det = 0
  · rw [h0, map_zero]
    exact re_det_nonneg (hA.add hP)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose] at hB
  have hBdet : B.det ≠ 0 := by
    intro hb
    apply h0
    rw [hB, det_mul, hb, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBHu : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hBdet)
  set Q := (B⁻¹)ᴴ * P * B⁻¹ with hQdef
  have hQ : Q.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same ((B⁻¹)ᴴ)
    simpa [hQdef, conjTranspose_conjTranspose] using this
  have hAP : A + P = Bᴴ * (1 + Q) * B := by
    rw [hQdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hB]
    congr 1
    rw [conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBHu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one]
  have hdet : (A + P).det = A.det * (1 + Q).det := by
    rw [hAP, hB, det_mul, det_mul, det_mul]
    ring
  have h1 := one_le_re_det_one_add hQ
  have h2 := re_det_nonneg hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, A.det = a := ⟨_, det_eq_ofReal_re hA⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (1 + Q).det = b := ⟨_, det_eq_ofReal_re (PosSemidef.one.add hQ)⟩
  rw [hdet, ha, hb, ← RCLike.ofReal_mul]
  simp only [RCLike.ofReal_re]
  rw [ha, RCLike.ofReal_re] at h2
  rw [hb, RCLike.ofReal_re] at h1
  nlinarith
end GroundTheory.Heights₂.Heights.MCDet
