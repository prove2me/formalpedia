-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.contDiffOn_zero_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:08.878672+00:00
-- url     : https://prove2.me/submissions/8b5d2765-e1fe-4006-a088-03f10dfc711e

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
theorem _root_.solution {V : Set X} {f : X → E} (h : ContinuousOn f V) : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) f V := by
  first
  | exact contDiffOn_zero.mpr h
  | (rw [Nat.cast_zero]; exact contDiffOn_zero.mpr h)
  | (simp only [Nat.cast_zero, CharP.cast_eq_zero]; exact contDiffOn_zero.mpr h)
end ReciprocityTheory.ChartRestriction.DS
