-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.nsq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:19:32.172162+00:00
-- url     : https://prove2.me/submissions/7ae795bd-c0ac-46f1-8103-71221f6ad4e3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) (y : Y) :
    0 ≤ A.nsq la F y := by
  unfold nsq; positivity
end ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
