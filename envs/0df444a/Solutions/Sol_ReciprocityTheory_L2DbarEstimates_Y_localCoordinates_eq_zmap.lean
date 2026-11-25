-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.localCoordinates_eq_zmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:25.028778+00:00
-- url     : https://prove2.me/submissions/9c1d40ef-f3c7-4bc3-94cb-49e636d010a9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ratio_pow_chart_independent
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by
  simp only [zLoc, zmap, (A.chart i).left_inv hi]
  congr 1
  funext k
  have := ratio_pow_chart_independent A la 1 (s k) w0 (by rw [one_nsmul]; exact hs k) hw i (A.pick y) y hi
    (A.mem_pick y)
  simpa using this
end ReciprocityTheory.L2DbarEstimates.Y
