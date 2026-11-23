-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.dbv_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:35.981137+00:00
-- url     : https://prove2.me/submissions/431890cc-caed-4d95-b2cb-72c9efb07b39

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hf : DifferentiableAt ℝ f (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dbv (fderiv ℝ (f ∘ Φ) v) ζ = dbv (fderiv ℝ f (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hf (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dbv]
end ReciprocityTheory.L2DbarEstimates.Y
