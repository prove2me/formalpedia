-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB.mop_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:13.988883+00:00
-- url     : https://prove2.me/submissions/54ab5cc7-9e4e-4cd9-883d-78b3b9758afd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H] [FiniteDimensional ℂ H]
  {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
  (ν : Measure K) [IsFiniteMeasure ν]
  (c : K → H →L[ℂ] H) (hc : Continuous c) {U Ω : Set H} (hU : IsOpen U) (hΩ : IsOpen Ω)
  (hUΩ : ∀ x ∈ U, ∀ k, c k x ∈ Ω)
omit [ProperSpace H] [FiniteDimensional ℂ H] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
theorem _root_.solution {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (L : K → E' →L[ℂ] E) (k : K) (T : H →L[ℂ] E') :
    Mop c L k T = (L k).comp (T.comp (c k)) := rfl
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
