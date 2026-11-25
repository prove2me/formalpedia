-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCSchur_qf_isLeast_1f825f941902
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:27.280561+00:00
-- url     : https://prove2.me/submissions/6cf11693-ecab-4703-bc49-c0ddd0119982

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCSchur
open Matrix
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GroundTheory.Heights₂.Heights.MCSchur
theorem _root_.solution (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (c : n → ℝ) :
    IsLeast (Set.range fun a : m → ℝ => qf Y⁻¹ (Sum.elim a c)) (qf (Y.toBlocks₂₂)⁻¹ c) := by
  have hZ : (Y⁻¹).PosDef := hY.inv
  set Z := Y⁻¹ with hZdef
  have hA : (Z.toBlocks₁₁).PosDef := hZ.submatrix Sum.inl_injective
  have hAu : IsUnit (Z.toBlocks₁₁).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have : Invertible Z.toBlocks₁₁ := hA.isUnit.invertible
  have h21 : Z.toBlocks₂₁ = (Z.toBlocks₁₂)ᴴ := by
    ext i j
    have := congrFun (congrFun hZ.1 (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply] using this.symm
  have hZeq : Z = fromBlocks Z.toBlocks₁₁ Z.toBlocks₁₂ (Z.toBlocks₁₂)ᴴ Z.toBlocks₂₂ := by
    rw [← h21, fromBlocks_toBlocks]
  have hS : (Y.toBlocks₂₂)⁻¹ = Z.toBlocks₂₂ - (Z.toBlocks₁₂)ᴴ * (Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂ := by
    rw [inv_toBlocks₂₂_eq Y ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit) hAu, h21]
  have key : ∀ a : m → ℝ, qf Z (Sum.elim a c) =
      qf Z.toBlocks₁₁ (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c) + qf (Y.toBlocks₂₂)⁻¹ c := by
    intro a
    have := schur_complement_eq₁₁ (A := Z.toBlocks₁₁) Z.toBlocks₁₂ Z.toBlocks₂₂ a c hA.1
    simp only [star_trivial] at this
    rw [hS, qf, qf, qf, dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec, ← this, ← hZeq]
  refine ⟨⟨-(((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c), ?_⟩, ?_⟩
  · simp only
    rw [key, neg_add_cancel]
    simp [qf]
  · rintro _ ⟨a, rfl⟩
    simp only
    rw [key]
    have := hA.posSemidef.dotProduct_mulVec_nonneg (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c)
    simp only [star_trivial] at this
    unfold qf
    linarith
end GroundTheory.Heights₂.Heights.MCSchur
