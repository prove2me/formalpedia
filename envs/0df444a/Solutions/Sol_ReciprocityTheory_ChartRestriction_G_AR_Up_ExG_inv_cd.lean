-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.inv_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:30:03.811983+00:00
-- url     : https://prove2.me/submissions/e4321fe7-186a-42a3-b5ec-8c6d1eed25db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPf
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustGPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExG_g_cd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (‖g1 y‖ ^ 2)⁻¹) z := by
  have h1 : ContDiffAt ℝ ∞ g1 z := (g_cd X x0 g1 hg hz).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun y => ‖g1 y‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt.comp z h1
  exact h2.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
