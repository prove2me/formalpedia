-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:30.26142+00:00
-- url     : https://prove2.me/submissions/89e1aee0-ccc3-4262-b293-281a172e28cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdFsq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_trace_ctm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_trace_mct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_entry_le_fsq
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
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M)
    (i j : Fin p ⊕ Fin q) :
    Complex.normSq (M i j) ≤ ((p + q : ℕ) + 1 : ℝ) * Complex.normSq (det M.toBlocks₂₂) := by
  obtain ⟨e1, e2, e3, e4⟩ := sumBdIsUpq_blocks h
  have hB := sumBd_detD_ge h
  have hBn := sumBdFsq_nonneg M.toBlocks₁₂
  have fD : sumBdFsq M.toBlocks₂₂ = q + sumBdFsq M.toBlocks₁₂ := by
    rw [← sumBd_trace_ctm, e2, trace_add, Complex.add_re, sumBd_trace_ctm]; simp
  have fA : sumBdFsq M.toBlocks₁₁ = p + sumBdFsq M.toBlocks₁₂ := by
    rw [← sumBd_trace_mct, e3, trace_add, Complex.add_re, sumBd_trace_mct]; simp
  have fA' : sumBdFsq M.toBlocks₁₁ = p + sumBdFsq M.toBlocks₂₁ := by
    rw [← sumBd_trace_ctm, e1, trace_add, Complex.add_re, sumBd_trace_ctm]; simp
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have key : ∀ X : ℝ, X ≤ (p + q : ℝ) + sumBdFsq M.toBlocks₁₂ →
      X ≤ ((p + q : ℕ) + 1 : ℝ) * Complex.normSq (det M.toBlocks₂₂) := by
    intro X hX; push_cast
    have hN1 : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by linarith
    nlinarith [mul_nonneg (add_nonneg hp hq) (sub_nonneg.mpr hN1)]
  apply key
  rcases i with a | a <;> rcases j with b | b
  · have := sumBd_entry_le_fsq M.toBlocks₁₁ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₁₂ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₂₁ a b
    exact le_trans this (by linarith)
  · have := sumBd_entry_le_fsq M.toBlocks₂₂ a b
    exact le_trans this (by linarith)
end ReciprocityTheory.ChartRestriction.G.AR.Up
