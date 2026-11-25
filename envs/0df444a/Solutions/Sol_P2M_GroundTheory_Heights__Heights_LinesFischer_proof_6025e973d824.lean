-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesFischer_proof_6025e973d824
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:02:58.25564+00:00
-- url     : https://prove2.me/submissions/323b3878-fecf-40d8-a186-a936dad2961f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesFischer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesFischer_toBlocks___eq_b092c100365c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_mono_86d278754b58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights
namespace LinesFischer
theorem _root_.solution : LinesFischer.Statement := by
  intro m k _ _ _ _ M hM
  have hA : M.toBlocks₁₁.PosDef := hM.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
  have hApos : 0 < M.toBlocks₁₁.det.re := MCDet.re_det_pos hA
  have hdet0 : M.toBlocks₁₁.det ≠ 0 := fun h => by simp [h] at hApos
  let _ : Invertible M.toBlocks₁₁ := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet0)
  have hMe : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    rw [← KLinesFischer.toBlocks₂₁_eq hM.1]
    exact (fromBlocks_toBlocks M).symm
  have hS : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).PosSemidef := by
    have h := hM.posSemidef
    rw [hMe] at h
    exact (PosDef.fromBlocks₁₁ _ _ hA).mp h
  have hdet : M.det = M.toBlocks₁₁.det *
      (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det := by
    conv_lhs => rw [hMe]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hmono : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det.re ≤
      M.toBlocks₂₂.det.re := by
    refine MCDet.re_det_mono hS ?_
    rw [sub_sub_cancel]
    exact hA.posSemidef.inv.conjTranspose_mul_mul_same _
  have him : M.toBlocks₁₁.det.im = 0 := by
    have h := congrArg Complex.im (MCDet.det_eq_ofReal_re hA.posSemidef)
    simpa using h
  rw [hdet, Complex.mul_re, him, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hApos.le
end LinesFischer
end GroundTheory.Heights₂.Heights
