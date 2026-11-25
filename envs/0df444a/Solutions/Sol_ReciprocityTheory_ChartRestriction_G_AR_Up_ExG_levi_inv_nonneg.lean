-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.levi_inv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:30:07.899874+00:00
-- url     : https://prove2.me/submissions/0ddb0453-8a41-4dee-ab0a-8c3021338d70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPf
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustGPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExG_two_le_inf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExG_g_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_normSq_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
theorem _root_.solution (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) z ξ).re := by
  have hfun : (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) = fun y => ((Complex.normSq ((g1 y)⁻¹) : ℝ) : ℂ) := by
    funext y
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hcd : ContDiffAt ℂ 2 (fun y => (g1 y)⁻¹) z := ((g_cd X x0 g1 hg hz).of_le two_le_inf).inv hne
  rw [hfun, leviV_normSq_comp hcd ξ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
