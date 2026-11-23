-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slmG_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:07.158804+00:00
-- url     : https://prove2.me/submissions/f99da633-4985-4cf0-a18d-a9270bf4a741

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) :
    slmG C fd w W = ∑ i, (C i (fd W)) • w i := by
  simp [slmG, ContinuousLinearMap.sum_apply]
end ReciprocityTheory.ChartRestriction.DS
