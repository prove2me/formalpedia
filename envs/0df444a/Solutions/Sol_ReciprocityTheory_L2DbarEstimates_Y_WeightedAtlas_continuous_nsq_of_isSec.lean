-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_nsq_of_isSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:14.206428+00:00
-- url     : https://prove2.me/submissions/cc689152-766c-49b6-82ab-59fcb742b92c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxL
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_aap_continuous_nsq

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
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {la : La} {u : ι → Y → ℂ} (hu : A.IsSec la u) :
    Continuous (A.nsq la u) := by
  exact A.aap_continuous_nsq la u (fun i j y hi hj => hu.2 i j y (Set.mem_univ y) hi hj)
    (fun i => (hu.1 i).continuousOn.mono fun v hv => ⟨hv, Set.mem_univ _⟩)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
