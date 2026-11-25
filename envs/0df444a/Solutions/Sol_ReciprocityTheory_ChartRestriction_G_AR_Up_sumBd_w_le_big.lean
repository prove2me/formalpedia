-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_w_le_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:16:18.058184+00:00
-- url     : https://prove2.me/submissions/e94e6ca8-7f93-44cc-bc6a-d04bbeb9cd65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdFsq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_detD_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_entry_bound


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
theorem _root_.solution {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) {s R : ℝ} (hs : 0 ≤ s)
    (hR : 0 < R) {i j : Fin p ⊕ Fin q} (hij : R < ‖M i j‖) :
    (Complex.normSq (det M.toBlocks₂₂))⁻¹ ^ s ≤ ((((p + q : ℕ) : ℝ) + 1) / R ^ 2) ^ s := by
  have h1 := sumBd_detD_ge h
  have h2 := sumBdFsq_nonneg M.toBlocks₁₂
  have hpos : 0 < Complex.normSq (det M.toBlocks₂₂) := by linarith
  have he := sumBd_entry_bound h i j
  have hR2 : R ^ 2 < Complex.normSq (M i j) := by
    have := Complex.normSq_eq_norm_sq (M i j)
    nlinarith [norm_nonneg (M i j)]
  have hc : (0 : ℝ) < ((p + q : ℕ) : ℝ) + 1 := by positivity
  have hle : (Complex.normSq (det M.toBlocks₂₂))⁻¹ ≤ (((p + q : ℕ) : ℝ) + 1) / R ^ 2 := by
    rw [inv_le_comm₀ hpos (by positivity), inv_div, div_le_iff₀ hc]
    linarith [mul_comm (Complex.normSq (det M.toBlocks₂₂)) (((p + q : ℕ) : ℝ) + 1)]
  exact Real.rpow_le_rpow (inv_nonneg.2 hpos.le) hle hs
end ReciprocityTheory.ChartRestriction.G.AR.Up
