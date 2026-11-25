-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplQuadDiag_proof_e419ec9470f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:15.744577+00:00
-- url     : https://prove2.me/submissions/1d9a8029-68d4-4771-a240-58992b180085

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplQuadDiag
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplQuadDiag_abs_det_eq_one_of_mul_transpose_83dc71c1c9f8

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SymplQuadDiag
theorem _root_.solution : SymplQuadDiag.Statement := by
  intro ι _ _ G hG
  have hH := hG.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [hUdef]
  refine ⟨star U, hH.eigenvalues, fun i => hG.eigenvalues_pos i, ?_, ?_, ?_⟩
  · rw [hstar]
    apply PSymplQuadDiag.abs_det_eq_one_of_mul_transpose
    rw [transpose_transpose, ← hstar]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · rw [hH.det_eq_prod_eigenvalues]
    simp
  · intro x
    have hx : x ᵥ* U = star U *ᵥ x := by rw [hstar, mulVec_transpose]
    calc qf G x = x ⬝ᵥ (U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x))) := by
          have hG' : G *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
            rw [mulVec_mulVec, mulVec_mulVec, ← hspec]
          rw [qf, hG']
      _ = (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
          rw [dotProduct_mulVec, hx]
      _ = ∑ i, hH.eigenvalues i * (star U *ᵥ x) i ^ 2 := by
          simp only [dotProduct, mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
            id]
          exact Finset.sum_congr rfl fun i _ => by ring
end SymplQuadDiag
end GroundTheory.Heights₂.Heights
