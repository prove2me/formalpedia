-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_exists_opens_preimage_subscheme__le_a66fe7f8493c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:48.362506+00:00
-- url     : https://prove2.me/submissions/27853d3a-370f-428b-9a14-e5e0fa090583

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (x : X)
    (hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : X.Opens, x ∈ U ∧ (Z.subschemeι ⁻¹ᵁ U) ≤ W := by
  have hind : Topology.IsInducing ⇑Z.subschemeι.base :=
    Z.subschemeι.isEmbedding.toIsInducing
  obtain ⟨t, ht, hteq⟩ := hind.isOpen_iff.mp W.isOpen
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  · have hwt : w ∈ ⇑Z.subschemeι.base ⁻¹' t := by
      rw [hteq]
      exact hw
    exact hwt
  · intro y hy
    have hy' : y ∈ ⇑Z.subschemeι.base ⁻¹' t := hy
    rw [hteq] at hy'
    exact hy'
end FunctorialResolution.EmbeddedResolution
