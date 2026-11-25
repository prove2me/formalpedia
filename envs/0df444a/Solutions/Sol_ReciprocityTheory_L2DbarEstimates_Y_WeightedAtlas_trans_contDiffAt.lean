-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.trans_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:25:39.580319+00:00
-- url     : https://prove2.me/submissions/f08b2a75-b91d-4770-8704-0d8727727150

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxE
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mem_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_trans_contDiffOn


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
theorem _root_.solution {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ 2 ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) :=
  ((A.trans_contDiffOn j i).contDiffAt ((A.isOpen_ovl j i).mem_nhds (A.mem_ovl hj hi))).of_le
    (by norm_cast)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
