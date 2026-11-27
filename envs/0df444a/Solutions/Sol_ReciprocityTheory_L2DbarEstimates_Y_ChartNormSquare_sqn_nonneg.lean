-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare.sqn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:31.93948+00:00
-- url     : https://prove2.me/submissions/ec41b232-284c-4a71-b8c5-51c08bf68cd1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AExact
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ChartNormSquare_nsq_nonneg

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
theorem _root_.solution {N : ℕ} (A : WeightedAtlas n Y ι La) (la : La) (w : Fin N → ι → Y → ℂ)
    (y : Y) : 0 ≤ A.sqn la w y :=
  Finset.sum_nonneg fun k _ => nsq_nonneg A la (w k) y
end ReciprocityTheory.L2DbarEstimates.Y.ChartNormSquare
