-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.differentiableAt_localCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:35.751876+00:00
-- url     : https://prove2.me/submissions/686c8d9c-a581-45b2-8eff-649df59ee398

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates

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
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hd : ∀ F : ι → Y → ℂ, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) (A.chart i y) := by
    intro F hF
    have := hF.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt hT)
  rw [differentiableAt_euclidean]
  intro k
  simp only [zLoc, PiLp.toLp_apply, div_eq_mul_inv]
  refine (hd (s k) (hs k)).mul ((hd w0 hw).inv ?_)
  simpa [(A.chart i).left_inv hi] using h0
end ReciprocityTheory.L2DbarEstimates.Y
