-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.chiC_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:44.055138+00:00
-- url     : https://prove2.me/submissions/1d7c1710-8f52-4fc5-83fe-51d7af80eb9e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_trans_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chiC_of_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chiC_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isCompact_chartImage
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chartImage_subset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {i : ι} {β : V n → ℝ} (hβ : ContDiff ℝ ∞ β) {K0 : Set (V n)}
    (hβs : ∀ u, β u ≠ 0 → u ∈ K0) (hK0 : IsCompact K0) (hK0t : K0 ⊆ (A.chart i).target) :
    A.SmoothFn (A.chiC i β) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  by_cases hx : (A.chart j).symm v ∈ (A.chart i).source
  · refine ⟨ovl A.chart j i, A.isOpen_ovl j i, ⟨hv, hx⟩, ?_⟩
    refine (hβ.comp_contDiffOn (((A.trans_contDiffOn j i).restrict_scalars ℝ).mono
      Set.inter_subset_right)).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_of_mem hv'.2.2
  · have hKc := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hxK : (A.chart j).symm v ∉ (A.chart i).symm '' K0 :=
      fun h => hx (A.chartImage_subset hK0t h)
    refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ((A.chart i).symm '' K0)ᶜ,
      (A.chart j).isOpen_inter_preimage_symm hKc.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_eq_zero hβs hv'.2.2
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
