-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:30:13.830464+00:00
-- url     : https://prove2.me/submissions/1f477851-4213-4293-8aae-68a1c591aad0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : P ⟶ Spec (CommRingCat.of k)) (H : P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData) {U : P.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (j₀ : Fin n) (S : Finset (Fin n))
    (hH : restrictIdeal H U = c.coordIdeal {j₀})
    (hZ : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
      Ideal.span
        ((fun j : Fin n =>
          (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
            (S : Set (Fin n)))) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.span (c.coord '' ((insert j₀ S : Finset (Fin n)) : Set (Fin n))) := by
  classical
  have happ : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl = H.subschemeι.app U := by
    rw [Scheme.Hom.appLE_eq_app]
  have hsurj : Function.Surjective (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom := by
    rw [happ]
    exact Scheme.IdealSheafData.subschemeι_app_surjective H ⟨U, hU⟩
  have hcomap : Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ⊥
      = H.ideal ⟨U, hU⟩ := by
    rw [happ, ← RingHom.ker_eq_comap_bot]
    exact Scheme.IdealSheafData.ker_subschemeι_app H ⟨U, hU⟩
  have hHspan : H.ideal ⟨U, hU⟩ = Ideal.span {c.coord j₀} := by
    rw [c.ideal_eq_span_coord hU H {j₀} hH, Finset.coe_singleton, Set.image_singleton]
  have key := ker_comp_subschemeι_ideal_eq_comap H Z hU
  rw [hZ] at key
  have himg : ((fun j : Fin n =>
        (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord j)) ''
          (S : Set (Fin n)))
      = (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin n))) :=
    (Set.image_image _ _ _).symm
  have hmap : Ideal.map (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (Ideal.span (c.coord '' (S : Set (Fin n))))
      = Ideal.span ((H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom ''
          (c.coord '' (S : Set (Fin n)))) :=
    Ideal.map_span _ _
  rw [key, himg, ← hmap, Ideal.comap_map_of_surjective _ hsurj, hcomap, hHspan,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
  exact le_antisymm (sup_le le_sup_right le_sup_left) (sup_le le_sup_right le_sup_left)
end FunctorialResolution.EmbeddedResolution
