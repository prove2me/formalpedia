-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:12:51.871191+00:00
-- url     : https://prove2.me/submissions/01ce126f-c68f-44de-8642-4b77325fb781

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Z : X.IdealSheafData)
    (h : ∀ x : X, x ∈ Z.support →
      ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : Finset (Fin n)),
        restrictIdeal Z U = c.coordIdeal S) :
    Smooth (Z.subschemeι ≫ p) := by
  classical
  have i3 : HasRingHomProperty (@Smooth.{u})
      (fun {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) => g.Smooth) := inferInstance
  have hloc : IsZariskiLocalAtSource (@Smooth.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ i3
  have key : ∀ y : ↥Z.subscheme, ∃ W : (Z.subscheme).Opens,
      y ∈ W ∧ Smooth (W.ι ≫ (Z.subschemeι ≫ p)) := by
    intro y
    have hy : Z.subschemeι.base y ∈ Z.support := by
      have hmem : Z.subschemeι.base y ∈ Set.range Z.subschemeι.base := Set.mem_range_self y
      simpa using hmem
    obtain ⟨U, hxU, n, c, S, hS⟩ := h _ hy
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
    have hV' : IsAffineOpen V := hV
    refine ⟨Z.subschemeι ⁻¹ᵁ V, hxV, ?_⟩
    exact smooth_ι_comp_subschemeι_comp_of_eq_coordIdeal Z hV' (c.restrict hVU) S
      (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S hS)
  choose W hyW hWsm using key
  have hsup : (⨆ y, W y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hyW y⟩
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top W hsup).mpr hWsm
end FunctorialResolution.EmbeddedResolution
