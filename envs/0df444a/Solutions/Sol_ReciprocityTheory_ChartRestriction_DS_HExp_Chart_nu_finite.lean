-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.nu_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:08.45178+00:00
-- url     : https://prove2.me/submissions/99698953-a41f-4f0c-8094-cc43df3936be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_expG_cont
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
theorem _root_.solution : IsFiniteMeasure (C.nu ρ μ) := by
  refine ⟨?_⟩
  rw [C.nu_apply hR μ MeasurableSet.univ]
  refine lt_of_le_of_lt (measure_mono (Set.image_mono ?_))
    (((isCompact_closedBall (0 : V) ρ).image C.expG_cont).measure_lt_top (μ := μ))
  exact fun x hx => ball_subset_closedBall hx.2
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
