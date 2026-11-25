-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:52.95308+00:00
-- url     : https://prove2.me/submissions/b6ca6c79-6400-4ddd-ade1-940637d923e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdFsq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_star_mul_self_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_detD_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    det M.toBlocks₂₂ ≠ 0 ∧
    (1 - (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)ᴴ).det.re =
      (Complex.normSq (det M.toBlocks₂₂))⁻¹ := by
  have e2 : M.toBlocks₂₂ᴴ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᴴ * M.toBlocks₁₂ :=
    (sumBdIsUpq_blocks h).2.1
  have hD1 : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by
    have := sumBd_detD_ge h; linarith [sumBdFsq_nonneg M.toBlocks₁₂]
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  have hD0 : det D ≠ 0 := by intro h0; rw [h0] at hD1; simp at hD1; linarith
  have hDu : IsUnit (det D) := isUnit_iff_ne_zero.mpr hD0
  refine ⟨hD0, ?_⟩
  have hinv : D * D⁻¹ = 1 := mul_nonsing_inv D hDu
  have hinvH : (D⁻¹)ᴴ * Dᴴ = 1 := by rw [← conjTranspose_mul, hinv, conjTranspose_one]
  have hW : 1 - (B * D⁻¹)ᴴ * (B * D⁻¹) = (D⁻¹)ᴴ * D⁻¹ := by
    have hBB : Bᴴ * B = Dᴴ * D - 1 := by rw [e2]; abel
    rw [conjTranspose_mul]
    calc 1 - (D⁻¹)ᴴ * Bᴴ * (B * D⁻¹) = 1 - (D⁻¹)ᴴ * (Bᴴ * B) * D⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 - ((D⁻¹)ᴴ * Dᴴ) * (D * D⁻¹) + (D⁻¹)ᴴ * D⁻¹ := by
          rw [hBB]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
          abel
      _ = (D⁻¹)ᴴ * D⁻¹ := by rw [hinv, hinvH, Matrix.one_mul]; abel
  rw [det_one_sub_mul_comm, hW, det_mul, det_conjTranspose, sumBd_star_mul_self_re,
    det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
end ReciprocityTheory.ChartRestriction.G.AR.Up
