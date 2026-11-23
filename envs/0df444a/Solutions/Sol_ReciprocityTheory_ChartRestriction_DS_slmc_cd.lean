-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slmc_cd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:07.78374+00:00
-- url     : https://prove2.me/submissions/61ad57da-1437-40b5-88fd-b572c2204a58

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hm : ContDiffOn ℝ ∞ m V) (i : Fin n × Fin n × Fin n × Bool) : ContDiffOn ℝ ∞ (slmc m i) V := by
  have h1 : ContDiffOn ℝ ∞ (fun q => m q i.1 i.2.2.1) V :=
    (slmEnt i.1 i.2.2.1).contDiff.comp_contDiffOn hm
  unfold slmc
  split_ifs
  · exact h1
  · exact contDiffOn_const.mul h1
end ReciprocityTheory.ChartRestriction.DS
