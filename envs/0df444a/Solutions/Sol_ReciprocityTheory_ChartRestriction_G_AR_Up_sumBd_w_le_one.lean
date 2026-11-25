-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_w_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:49.369425+00:00
-- url     : https://prove2.me/submissions/8b021ce4-f76d-4457-9a23-1a049c988bb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdFsq_nonneg
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
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ∧ (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ≤ 1 := by
  have h1 := sumBd_detD_ge h
  have h2 := sumBdFsq_nonneg M.toBlocks₁₂
  have hN : 1 ≤ Complex.normSq (det M.toBlocks₂₂) := by linarith
  have hpos : 0 < Complex.normSq (det M.toBlocks₂₂) := by linarith
  have hinv : (Complex.normSq (det M.toBlocks₂₂))⁻¹ ≤ 1 := by
    first
      | exact inv_le_one_of_one_le₀ hN
      | exact inv_le_one hN
  exact ⟨Real.rpow_nonneg (inv_nonneg.2 hpos.le) _, Real.rpow_le_one (inv_nonneg.2 hpos.le) hinv hs⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up
