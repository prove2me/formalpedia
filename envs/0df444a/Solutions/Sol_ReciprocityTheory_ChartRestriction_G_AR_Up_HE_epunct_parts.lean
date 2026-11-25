-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.epunct_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:07.951319+00:00
-- url     : https://prove2.me/submissions/eaed31be-dc9c-4c66-a3ed-9b6902bdb3f8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_normSq_contDiffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_HE_contDiffAt_of_punct
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
variable {U : Set (V n)}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE
theorem _root_.solution (hU : IsOpen U) {e : V n → ℝ} (he : ContDiffOn ℝ ∞ e U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) {y : V n} (hy : y ∈ U) (hgy : g y ≠ 0) :
    ContDiffAt ℝ ∞ e y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (1 + Complex.normSq (g w))) y ∧
      ContDiffAt ℝ ∞ (fun w => Real.log (Complex.normSq (g w))) y := by
  have hN := normSq_contDiffAt (contDiffAt_of_punct hU hg hy)
  refine ⟨he.contDiffAt (hU.mem_nhds hy), ?_, ?_⟩
  · refine (contDiffAt_const.add hN).log ?_
    have h0 := Complex.normSq_nonneg (g y)
    have h1 : (0 : ℝ) < 1 + Complex.normSq (g y) := by linarith
    exact h1.ne'
  · exact hN.log (Complex.normSq_pos.mpr hgy).ne'
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
