-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCSchur_inv_toBlocks___eq_c87d050c0061
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:24.044972+00:00
-- url     : https://prove2.me/submissions/8f4ec466-e51a-45ac-97c9-7257298871f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast

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
theorem _root_.solution (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : IsUnit Y.det)
    (hA : IsUnit (Y⁻¹).toBlocks₁₁.det) :
    (Y.toBlocks₂₂)⁻¹ = (Y⁻¹).toBlocks₂₂ - (Y⁻¹).toBlocks₂₁ * ((Y⁻¹).toBlocks₁₁)⁻¹ * (Y⁻¹).toBlocks₁₂ := by
  set Z := Y⁻¹ with hZ
  have hYZ : Y * Z = 1 := Matrix.mul_nonsing_inv Y hY
  rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks Z, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at hYZ
  obtain ⟨-, -, h21, h22⟩ := hYZ
  apply Matrix.inv_eq_right_inv
  have e : Y.toBlocks₂₁ = -(Y.toBlocks₂₂ * Z.toBlocks₂₁) * (Z.toBlocks₁₁)⁻¹ := by
    have := congrArg (· * (Z.toBlocks₁₁)⁻¹) h21
    simp only [Matrix.add_mul, Matrix.zero_mul] at this
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hA] at this
    rw [Matrix.neg_mul]
    exact eq_neg_of_add_eq_zero_left this
  rw [Matrix.mul_sub, ← h22, e]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel
end GroundTheory.Heights₂.Heights.MCSchur
