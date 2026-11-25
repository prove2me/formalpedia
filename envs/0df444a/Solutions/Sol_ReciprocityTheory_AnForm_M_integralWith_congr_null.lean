-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integralWith_congr_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:12.958911+00:00
-- url     : https://prove2.me/submissions/53a66bcf-c967-45b7-a06f-e90c7cb0b745

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Theorems.Thm_ReciprocityTheory_AnForm_M_analyticNull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by
  first
  | unfold integralWith
  | simp only [integralWith]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hnull : volume ((A.chart j) '' (S ∩ (A.chart j).source)) = 0 :=
    analyticNull A S hS hint j
  have hsub : {y | ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y)} ∩
      (A.chart j).target ⊆ (A.chart j) '' (S ∩ (A.chart j).source) := by
    intro y hy
    have hne : ¬(P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
        P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y) := hy.1
    have hyt : y ∈ (A.chart j).target := hy.2
    refine ⟨(A.chart j).symm y, ⟨?_, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
    by_contra hnS
    apply hne
    rw [hg _ hnS]
  have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target),
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y =
      P.χ j ((A.chart j).symm y) * g' ((A.chart j).symm y) * locDens A Φ j y := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply' hT]
    exact MeasureTheory.measure_mono_null hsub hnull
  exact MeasureTheory.integral_congr_ae hae
end ReciprocityTheory.AnForm.M
