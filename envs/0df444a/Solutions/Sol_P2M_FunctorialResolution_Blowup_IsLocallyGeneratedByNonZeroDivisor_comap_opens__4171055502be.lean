-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_opens__4171055502be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:03.999426+00:00
-- url     : https://prove2.me/submissions/4ec11ef4-8fcf-4df5-b980-981439d71912

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_FunctorialResolution_Blowup_map_mem_nonZeroDivisors_of_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
private theorem exists_affineOpen_mem_subset (Z : Scheme.{u}) (x : Z) (W : Z.Opens)
    (hx : x ∈ W) : ∃ V : Z.affineOpens, x ∈ (V : Z.Opens) ∧ (V : Z.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩
private theorem coe_image_of_isOpenImmersion {X' Y' : Scheme.{u}} (f : X' ⟶ Y')
    [IsOpenImmersion f] (V : X'.Opens) :
    ((f ''ᵁ V : Y'.Opens) : Set Y') = f.base '' (V : Set X') := rfl
private theorem coe_preimage_opens {X' Y' : Scheme.{u}} (f : X' ⟶ Y') (V : Y'.Opens) :
    ((f ⁻¹ᵁ V : X'.Opens) : Set X') = f.base ⁻¹' (V : Set Y') := rfl
private theorem range_opensι {Y' : Scheme.{u}} (U : Y'.Opens) :
    Set.range U.ι.base = (U : Set Y') := U.range_ι
private theorem image_opensι_le {Y' : Scheme.{u}} (U : Y'.Opens) (V : U.toScheme.Opens) :
    (U.ι ''ᵁ V : Y'.Opens) ≤ U := by
  intro z hz
  have hz' : z ∈ U.ι.base '' (V : Set U.toScheme) := hz
  obtain ⟨w, -, rfl⟩ := hz'
  have hr : U.ι.base w ∈ Set.range U.ι.base := Set.mem_range_self w
  rw [range_opensι] at hr
  exact hr
private theorem image_preimage_opensι {Y' : Scheme.{u}} (U : Y'.Opens) (D : Y'.Opens)
    (hD : D ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
  apply TopologicalSpace.Opens.ext
  rw [coe_image_of_isOpenImmersion, coe_preimage_opens, Set.image_preimage_eq_inter_range,
    range_opensι]
  exact Set.inter_eq_self_of_subset_left hD
private theorem basicOpen_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U : Y'.Opens}
    {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y', U)) :
    X'.basicOpen ((f.appLE U V h).hom r) = V ⊓ f ⁻¹ᵁ (Y'.basicOpen r) := by
  have h1 : (f.appLE U V h).hom r
      = (X'.presheaf.map (homOfLE h).op).hom ((f.app U).hom r) := rfl
  rw [h1, Scheme.basicOpen_res, Scheme.preimage_basicOpen]
private theorem restrictAppIso_hom {Y' : Scheme.{u}} (U : Y'.Opens) (V : U.toScheme.Opens) :
    (sectionsOpensImageIso U V).hom
      = U.ι.appLE (U.ι ''ᵁ V) V (U.ι.preimage_image_eq V).ge :=
  Scheme.Hom.appIso_hom' U.ι V
private theorem map_comp_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {U₁ U₂ : Y'.Opens}
    (e : U₁ ≤ U₂) {V : X'.Opens} (h : V ≤ f ⁻¹ᵁ U₁) (h' : V ≤ f ⁻¹ᵁ U₂) :
    Y'.presheaf.map (homOfLE e).op ≫ f.appLE U₁ V h = f.appLE U₂ V h' :=
  Scheme.Hom.map_appLE f h (homOfLE e).op
variable {X X₁ : Scheme.{u}}
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {F : Y.IdealSheafData} (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    (U : Y.Opens) : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor (F.comap U.ι) := by
  intro x
  obtain ⟨W, t, hyW, ht, hFW⟩ := hF (U.ι.base x)
  obtain ⟨V₀, hxV₀, hV₀⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_subset U.toScheme x (U.ι ⁻¹ᵁ (W : Y.Opens)) hyW
  have hD₀aff : IsAffineOpen (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) :=
    V₀.2.image_of_isOpenImmersion U.ι
  have hyD₀ : U.ι.base x ∈ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := ⟨x, hxV₀, rfl⟩
  obtain ⟨a, b, hab, hya⟩ :=
    exists_basicOpen_le_affine_inter W.2 hD₀aff (U.ι.base x) ⟨hyW, hyD₀⟩
  have hDD₀ : Y.basicOpen a ≤ U.ι ''ᵁ (V₀ : U.toScheme.Opens) := by
    rw [hab]
    exact Y.basicOpen_le b
  have hDU : Y.basicOpen a ≤ U := hDD₀.trans (EmbeddedResolution.image_opensι_le U (V₀ : U.toScheme.Opens))
  have hDW : Y.basicOpen a ≤ (W : Y.Opens) := Y.basicOpen_le a
  have hpreV₀ : U.ι ⁻¹ᵁ (Y.basicOpen a) ≤ (V₀ : U.toScheme.Opens) := by
    intro z hz
    have h2 : z ∈ U.ι ⁻¹ᵁ (U.ι ''ᵁ (V₀ : U.toScheme.Opens)) := hDD₀ hz
    rwa [U.ι.preimage_image_eq] at h2
  have hV₁eq : U.toScheme.basicOpen
      ((U.ι.appLE (W : Y.Opens) (V₀ : U.toScheme.Opens) hV₀).hom a)
      = U.ι ⁻¹ᵁ (Y.basicOpen a) := by
    rw [_root_.FunctorialResolution.EmbeddedResolution.basicOpen_appLE]
    exact inf_eq_right.mpr hpreV₀
  have hV₁aff : IsAffineOpen (U.ι ⁻¹ᵁ (Y.basicOpen a)) := by
    rw [← hV₁eq]
    exact V₀.2.basicOpen _
  have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a)) = Y.basicOpen a :=
    EmbeddedResolution.image_preimage_opensι U (Y.basicOpen a) hDU
  have himgW : (U.ι ''ᵁ (U.ι ⁻¹ᵁ (Y.basicOpen a))) ≤ (W : Y.Opens) := by
    rw [himg]
    exact hDW
  have hleW : (U.ι ⁻¹ᵁ (Y.basicOpen a)) ≤ U.ι ⁻¹ᵁ (W : Y.Opens) := fun z hz => hDW hz
  refine ⟨⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩,
    (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t, hya, ?_, ?_⟩
  · have := W.2.isLocalization_basicOpen a
    have ht' : (Y.presheaf.map (homOfLE hDW).op).hom t
        ∈ nonZeroDivisors Γ(Y, Y.basicOpen a) :=
      IsLocalization.nonZeroDivisors_le_comap (.powers a) Γ(Y, Y.basicOpen a) ht
    have hmor : Y.presheaf.map (homOfLE hDW).op ≫ Y.presheaf.map (eqToHom himg).op ≫
        (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom
        = U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW := by
      rw [EmbeddedResolution.restrictAppIso_hom, ← Category.assoc, ← Functor.map_comp]
      have h3 : eqToHom himg ≫ homOfLE hDW = homOfLE himgW := Subsingleton.elim _ _
      have h3' : (homOfLE hDW).op ≫ (eqToHom himg).op = (homOfLE himgW).op := by
        rw [← op_comp, h3]
      rw [h3']
      exact EmbeddedResolution.map_comp_appLE U.ι himgW _ hleW
    have hfin : (U.ι.appLE (W : Y.Opens) (U.ι ⁻¹ᵁ (Y.basicOpen a)) hleW).hom t
        = (_root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))).hom.hom
            ((Y.presheaf.map (eqToHom himg).op).hom
              ((Y.presheaf.map (homOfLE hDW).op).hom t)) := by
      rw [← hmor]
      rfl
    rw [hfin]
    exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso
      (Y.presheaf.mapIso (eqToIso himg).op ≪≫ _root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U (U.ι ⁻¹ᵁ (Y.basicOpen a))) ht'
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE F U.ι W
      ⟨U.ι ⁻¹ᵁ (Y.basicOpen a), hV₁aff⟩ hleW, hFW, Ideal.map_span, Set.image_singleton]
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
