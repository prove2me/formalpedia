-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.tendsto_ofReal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:58.857201+00:00
-- url     : https://prove2.me/submissions/df5f364e-4df5-4674-802a-c86fbc83c2ae

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
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have := h.tendsto 0
  simp only [mul_zero, add_zero, one_pow, ENNReal.ofReal_one] at this
  exact this.mono_left nhdsWithin_le_nhds
end ReciprocityTheory.ChartRestriction.DS.HExp
