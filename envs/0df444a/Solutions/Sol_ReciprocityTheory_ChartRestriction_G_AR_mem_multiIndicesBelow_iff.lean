-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:38:15.528403+00:00
-- url     : https://prove2.me/submissions/d1ea41e9-4abb-4a03-891f-f9ea49d3bfe7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.ChartRestriction.G.AR
theorem _root_.solution {a0 : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a0 ↔ ∑ k, α k < a0 := by
  simp [multiLt, Finset.Nat.mem_antidiagonalTuple]
end ReciprocityTheory.ChartRestriction.G.AR
