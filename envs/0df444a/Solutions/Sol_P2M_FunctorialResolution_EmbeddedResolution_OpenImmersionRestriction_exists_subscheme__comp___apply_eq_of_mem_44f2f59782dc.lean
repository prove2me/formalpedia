-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_exists_subscheme__comp___apply_eq_of_mem_44f2f59782dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:51.990382+00:00
-- url     : https://prove2.me/submissions/793adc6f-201a-4a0e-b5bf-a2aba6bf4eab

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) (T : Set ↥W)
    (hT : U.ι.base ⁻¹' T ⊆ (D.support : Set ↥(U.toScheme)))
    (x : ↥W) (hxU : x ∈ (U : Set ↥W)) (hxT : x ∈ T) :
    ∃ y : ↥(D.subscheme), (D.subschemeι ≫ U.ι).base y = x := by
  have hx : x ∈ Set.range ⇑U.ι.base := by
    rw [hV.range_ι W U]
    exact hxU
  obtain ⟨y₀, hy₀⟩ := hx
  have hy₀T : y₀ ∈ (D.support : Set ↥(U.toScheme)) := by
    refine hT ?_
    have h' : U.ι.base y₀ ∈ T := by
      rw [hy₀]
      exact hxT
    exact h'
  have hy₀r : y₀ ∈ Set.range ⇑D.subschemeι.base := by
    rw [hV.range_subschemeι U.toScheme D]
    exact hy₀T
  obtain ⟨y, hy⟩ := hy₀r
  refine ⟨y, ?_⟩
  rw [hV.base_comp _ _ _ D.subschemeι U.ι y, hy, hy₀]
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
