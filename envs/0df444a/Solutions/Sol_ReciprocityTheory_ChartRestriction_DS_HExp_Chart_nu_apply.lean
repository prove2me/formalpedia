-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.nu_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:34.474803+00:00
-- url     : https://prove2.me/submissions/ac69e30f-d434-4f75-ad2c-0f2d94ef70b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_injOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_meas_image

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
include hR
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  have hinj : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) := fun x y h =>
    Subtype.ext (C.injOn hR x.2 y.2 h)
  have hm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [this]
    refine C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht) ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rw [nu, Measure.map_apply measurable_subtype_coe hs,
    Measure.comap_apply _ hinj hm _ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hX, hXρ⟩, rfl⟩
    exact ⟨⟨X, hXρ⟩, hX, rfl⟩
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
