-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_inv_le_of_ge_22d5970a02ea
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:09.358031+00:00
-- url     : https://prove2.me/submissions/d4bb628b-089d-4730-9a3f-a0e75cdb13ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by
  have hA : A.PosDef := posDef_of_ge hc h
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_smul_one_sub]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := quad_nonneg h y
      rw [quad_sub_smul_one, hx, dotProduct_comm] at this
      linarith
    have h3 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := dot_self_nonneg _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h3
    have key : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
    linarith
end GroundTheory.Heights₂.Heights.MCBounds
