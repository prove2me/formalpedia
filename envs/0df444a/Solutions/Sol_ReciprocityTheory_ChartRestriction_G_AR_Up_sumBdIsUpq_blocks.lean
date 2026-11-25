-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:37.168093+00:00
-- url     : https://prove2.me/submissions/8e4a3ec4-a541-4ffc-baf0-e5c9f34c456c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_right

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
    M.toBlocks₁₁ᴴ * M.toBlocks₁₁ = 1 + M.toBlocks₂₁ᴴ * M.toBlocks₂₁ ∧
    M.toBlocks₂₂ᴴ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᴴ * M.toBlocks₁₂ ∧
    M.toBlocks₁₁ * M.toBlocks₁₁ᴴ = 1 + M.toBlocks₁₂ * M.toBlocks₁₂ᴴ ∧
    M.toBlocks₂₂ * M.toBlocks₂₂ᴴ = 1 + M.toBlocks₂₁ * M.toBlocks₂₁ᴴ := by
  have h1 := h
  have h2 := sumBdIsUpq_right h
  rw [IsUpq, ← fromBlocks_toBlocks M] at h1
  rw [← fromBlocks_toBlocks M] at h2
  simp only [Jf, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj] at h1 h2
  simp at h1 h2
  obtain ⟨a1, -, -, a4⟩ := h1
  obtain ⟨b1, -, -, b4⟩ := h2
  have a4' := congrArg Neg.neg a4
  have b4' := congrArg Neg.neg b4
  rw [neg_neg] at a4' b4'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← a1]; abel
  · rw [← a4']; abel
  · rw [← b1]; abel
  · rw [← b4']; abel
end ReciprocityTheory.ChartRestriction.G.AR.Up
