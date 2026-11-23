-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.tendsto_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:58.949804+00:00
-- url     : https://prove2.me/submissions/a84e048d-5790-42eb-a65d-73560bf79091

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ht hr
end ReciprocityTheory.ChartRestriction.DS.HExp
