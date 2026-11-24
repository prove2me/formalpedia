-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:15.177271+00:00
-- url     : https://prove2.me/submissions/b3e17048-563d-4bb9-8529-d685e4c5408a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_dot_self_nonneg_1b107a996ff0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_smul_one_sub_79ae7301e3b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_sub_smul_one_15ab2baf7d6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_symm_4b25d90b3d61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_sub_smul_one]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hcs := quad_cs hA.posSemidef y x
    have e1 : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ x := by rw [← quad_symm hs, hx]
    have e2 : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by rw [hx, dotProduct_comm]
    rw [e1, e2] at hcs
    have hxy : 0 ≤ x ⬝ᵥ y := e2 ▸ quad_nonneg hA.posSemidef y
    have hlx : x ⬝ᵥ (A *ᵥ x) ≤ l * (x ⬝ᵥ x) := by
      have := quad_nonneg h x
      rw [quad_smul_one_sub] at this
      linarith
    have hxx := dot_self_nonneg x
    rcases hxx.lt_or_eq with hpos | hzero
    · have h4 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ (l * (x ⬝ᵥ y)) * (x ⬝ᵥ x) := by
        nlinarith [mul_le_mul_of_nonneg_left hlx hxy]
      have h5 : x ⬝ᵥ x ≤ l * (x ⬝ᵥ y) := le_of_mul_le_mul_right h4 hpos
      have := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hl.le)
      rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      linarith
    · rw [← hzero]; simpa using hxy
end GroundTheory.Heights₂.Heights.MCBounds
