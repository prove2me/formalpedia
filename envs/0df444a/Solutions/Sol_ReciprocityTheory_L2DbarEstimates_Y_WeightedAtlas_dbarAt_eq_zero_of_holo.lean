-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.dbarAt_eq_zero_of_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:18.773871+00:00
-- url     : https://prove2.me/submissions/9c0d29ae-d754-44e5-96c0-17c73f48c4a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_dbarAt_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_dbv_holo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (j : ι) (F : ι → Y → ℂ) (y : Y) {G : V n → ℂ}
    (hF : (F j ∘ (A.chart j).symm) =ᶠ[𝓝 (A.chart j y)] G) (hG : DifferentiableAt ℂ G (A.chart j y))
    (ξ : Fin n → ℂ) : A.dbarAt j F y ξ = 0 := by
  rw [dbarAt_eq, hF.fderiv_eq, dbv_holo hG]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
