-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:53.457379+00:00
-- url     : https://prove2.me/submissions/acc33a91-bf38-41c6-89b9-110780e3be41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.MCCusp
theorem _root_.solution {Z : Matrix ι ι ℝ} (hZ : Z.PosDef) (x : ι → ℝ) (i : ι) :
    x i ^ 2 ≤ Z⁻¹ i i * qf Z x := by
  have hs := transpose_eq_of_posSemidef hZ.posSemidef
  have hu : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det _).mp hZ.isUnit
  set w := Z⁻¹ *ᵥ Pi.single i 1 with hw
  have hZw : Z *ᵥ w = Pi.single i 1 := by
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h1 : w ⬝ᵥ (Z *ᵥ x) = x i := by
    rw [dot_mulVec_symm hs, hZw, dotProduct_single, mul_one]
  have h2 : qf Z w = Z⁻¹ i i := by
    rw [qf, hZw, dotProduct_single, mul_one, hw, mulVec_single]
    simp
  have := bil_sq_le hZ.posSemidef x w
  rwa [h1, h2] at this
end GroundTheory.Heights₂.Heights.MCCusp
