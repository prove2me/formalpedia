-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_Chart_nu_apply_3ee47408ca0b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:25.697639+00:00
-- url     : https://prove2.me/submissions/a0315fff-e7b9-40e7-9221-e18fbc4545f3

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_injOn_8b27bc3b6990
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_meas_image_7b6998579755

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open Formalism.BasicNotions.Examples₂.CD.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
include hR
namespace Formalism.BasicNotions.Examples₂.CD.Chart
theorem _root_.solution {s : Set V} (hs : MeasurableSet s) :
    C.nu ρ μ s = μ (C.expG '' (s ∩ ball 0 ρ)) := by
  unfold nu
  rw [Measure.map_apply measurable_subtype_coe hs]
  have hf : Function.Injective (fun x : ball (0 : V) ρ => C.expG x.1) :=
    fun a b h => Subtype.ext (C.injOn hR a.2 b.2 h)
  have hfm : ∀ t : Set (ball (0 : V) ρ), MeasurableSet t →
      MeasurableSet ((fun x : ball (0 : V) ρ => C.expG x.1) '' t) := by
    intro t ht
    have h1 : (fun x : ball (0 : V) ρ => C.expG x.1) '' t = C.expG '' (Subtype.val '' t) := by
      rw [Set.image_image]
    rw [h1]
    exact C.meas_image hR (MeasurableSet.subtype_image measurableSet_ball ht)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  rw [Measure.comap_apply _ hf hfm μ (measurable_subtype_coe hs)]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
  · rintro ⟨X, ⟨hXs, hXb⟩, rfl⟩
    exact ⟨⟨X, hXb⟩, hXs, rfl⟩
end Formalism.BasicNotions.Examples₂.CD.Chart
