-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_comap_7e7349a281e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:02:14.136344+00:00
-- url     : https://prove2.me/submissions/4ff2a352-92a9-4d72-9c4d-bc521e736169

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
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {P : Scheme.{u}}
private theorem ker_ideal_eq_ker_appLE {A B : Scheme.{u}} (f : A ⟶ B) [QuasiCompact f]
    (V : B.affineOpens) :
    f.ker.ideal V = RingHom.ker (f.appLE (V : B.Opens) (f ⁻¹ᵁ (V : B.Opens)) le_rfl).hom := by
  simp only [Scheme.Hom.appLE_eq_app]
  simp
private theorem ker_appLE_congr {A B : Scheme.{u}} (f : A ⟶ B) (W : B.Opens)
    {V₁ V₂ : A.Opens} (h : V₁ = V₂) (e₁ : V₁ ≤ f ⁻¹ᵁ W) (e₂ : V₂ ≤ f ⁻¹ᵁ W) :
    RingHom.ker (f.appLE W V₁ e₁).hom = RingHom.ker (f.appLE W V₂ e₂).hom := by
  subst h
  rfl
variable {k : Type u} [Field k]
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData)
    {U : P.Opens} (hU : IsAffineOpen U) :
    (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      Ideal.comap (H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl).hom
        (Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩) := by
  have hqcZ : QuasiCompact Z.subschemeι := inferInstance
  have hqcf : QuasiCompact (Z.subschemeι ≫ H.subschemeι) := inferInstance
  have hopen : (Z.subschemeι ≫ H.subschemeι) ⁻¹ᵁ U
      = Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U) :=
    Scheme.Hom.comp_preimage ..
  have hle : Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)
      ≤ (Z.subschemeι ≫ H.subschemeι) ⁻¹ᵁ U := le_of_eq hopen.symm
  have h1 : (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨U, hU⟩ =
      RingHom.ker ((Z.subschemeι ≫ H.subschemeι).appLE U
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) hle).hom :=
    (ker_ideal_eq_ker_appLE (Z.subschemeι ≫ H.subschemeι) ⟨U, hU⟩).trans
      (ker_appLE_congr (Z.subschemeι ≫ H.subschemeι) U hopen le_rfl hle)
  have h2 : Z.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩ =
      RingHom.ker (Z.subschemeι.appLE (H.subschemeι ⁻¹ᵁ U)
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) le_rfl).hom :=
    (congrArg (fun I : H.subscheme.IdealSheafData =>
        I.ideal ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩)
      (Scheme.IdealSheafData.ker_subschemeι Z)).symm.trans
      (ker_ideal_eq_ker_appLE Z.subschemeι
        ⟨H.subschemeι ⁻¹ᵁ U, isAffineOpen_preimage_subschemeι H hU⟩)
  have hcomp : H.subschemeι.appLE U (H.subschemeι ⁻¹ᵁ U) le_rfl ≫
      Z.subschemeι.appLE (H.subschemeι ⁻¹ᵁ U)
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) le_rfl
      = (Z.subschemeι ≫ H.subschemeι).appLE U
        (Z.subschemeι ⁻¹ᵁ (H.subschemeι ⁻¹ᵁ U)) hle := by
    simp only [Scheme.Hom.appLE_comp_appLE]
  rw [h1, h2, ← hcomp, CommRingCat.hom_comp]
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_comap, RingHom.comp_apply]
end FunctorialResolution.EmbeddedResolution
