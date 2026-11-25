-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_coeFn_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:21.668934+00:00
-- url     : https://prove2.me/submissions/cd198840-0f6c-4e31-ade3-343df4bf6f28

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
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  · intro i t hi ih
    rw [Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp only [Pi.add_apply, hx, Finset.sum_insert hi]
end ReciprocityTheory.ChartRestriction.DS
