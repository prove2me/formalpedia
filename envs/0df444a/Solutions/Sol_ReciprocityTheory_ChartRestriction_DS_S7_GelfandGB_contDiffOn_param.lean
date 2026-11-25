-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB.contDiffOn_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:17.132336+00:00
-- url     : https://prove2.me/submissions/7e14b19e-ac39-458b-8bc0-6093d05bce64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_contDiffOn_param_nat

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
include hc hU hΩ hUΩ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
theorem _root_.solution {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E)
    (hf : ContDiffOn ℂ ∞ f Ω) (hL : Continuous L) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, L k (f (c k x)) ∂ν) U :=
  contDiffOn_infty.mpr fun m => contDiffOn_param_nat ν c hc hU hΩ hUΩ m f L hf hL
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
