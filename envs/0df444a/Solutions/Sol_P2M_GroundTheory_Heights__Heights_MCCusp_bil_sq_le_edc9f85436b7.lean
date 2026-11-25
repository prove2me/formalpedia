-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:06.130224+00:00
-- url     : https://prove2.me/submissions/80f6e535-a158-44f5-a158-73e08623440b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_dot_mulVec_symm_9b8f1a0cd591
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda

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
namespace GroundTheory.Heights₂.Heights.MCCusp
theorem _root_.solution {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u w : ι → ℝ) :
    (w ⬝ᵥ (Z *ᵥ u)) ^ 2 ≤ qf Z w * qf Z u := by
  have hs := transpose_eq_of_posSemidef hZ
  have key : ∀ x : ℝ, 0 ≤ qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
    intro x
    have h := qf_nonneg hZ (u - x • w)
    have e : qf Z (u - x • w) = qf Z w * (x * x) + (-2 * (w ⬝ᵥ (Z *ᵥ u))) * x + qf Z u := by
      simp only [qf, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dot_mulVec_symm hs u w]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith
end GroundTheory.Heights₂.Heights.MCCusp
