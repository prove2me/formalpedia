-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.nu_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:11.516647+00:00
-- url     : https://prove2.me/submissions/fa0bb603-6e51-49ea-ab4b-2d97413fb9b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_exp_logA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_logA_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrict_logA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_mat_expG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_nu_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
include hR
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution (hρ : 0 < ρ) (r : ℝ) (hr : 0 < r) : 0 < C.nu ρ μ (closedBall (0 : V) r) := by
  rw [C.nu_apply hR μ measurableSet_closedBall]
  have hc : ContinuousAt (logA 𝔸) (1 : 𝔸) := hasStrict_logA.hasFDerivAt.continuousAt
  have h1 : ∀ᶠ h in 𝓝 (1 : 𝔸), ‖logA 𝔸 h‖ < min r ρ := by
    have := hc.eventually (Metric.ball_mem_nhds (logA 𝔸 (1 : 𝔸)) (lt_min hr hρ))
    simpa [logA_one] using this
  have h2 : Tendsto C.mat (𝓝 (1 : G)) (𝓝 (1 : 𝔸)) := by
    have := C.emb.continuous.tendsto 1
    rwa [map_one] at this
  have h3 := h2.eventually (h1.and exp_logA)
  refine lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds μ h3) (measure_mono ?_)
  intro g hg
  have hg1 : ‖logA 𝔸 (C.mat g)‖ < min r ρ := hg.1
  have hg2 : exp (logA 𝔸 (C.mat g)) = C.mat g := hg.2
  have hV : logA 𝔸 (C.mat g) ∈ V := (hR _ (lt_of_lt_of_le hg1 (min_le_right _ _))).2 ⟨g, hg2.symm⟩
  refine ⟨⟨_, hV⟩, ⟨?_, ?_⟩, C.emb.injective (by rw [mat_expG]; exact hg2)⟩
  · rw [mem_closedBall_zero_iff]; exact (lt_of_lt_of_le hg1 (min_le_left _ _)).le
  · rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hg1 (min_le_right _ _)
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
