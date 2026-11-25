-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_isOpen_image_of_cover_3f74170e1f04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:34.235087+00:00
-- url     : https://prove2.me/submissions/6ba81f40-6878-4a15-9579-e6f9166c7472

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
theorem _root_.solution {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ) (hcov : IsCoveringMap hmaps.restrict)
    (O : Set X) (hO : IsOpen O) (hOM : O ⊆ M₀) : IsOpen (q '' O) := by
  have h1 : IsOpen (hmaps.restrict '' (Subtype.val ⁻¹' O : Set M₀)) :=
    hcov.isOpenMap _ (hO.preimage continuous_subtype_val)
  have h2 := hΔ.isOpen_compl.isOpenMap_subtype_val _ h1
  convert h2 using 1
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hOM hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
end GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
