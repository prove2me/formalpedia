-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData.K_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:15.678069+00:00
-- url     : https://prove2.me/submissions/5ed815f4-8944-48cf-ac5d-7ac70b4f767b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isCompact_chartImage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
variable {A}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
theorem _root_.solution {P : Y} (hP : P ∈ Sf) : IsCompact (D.K P) :=
  A.isCompact_chartImage (isCompact_closedBall _ _) fun _ hu => (D.sub P hP hu).1
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
