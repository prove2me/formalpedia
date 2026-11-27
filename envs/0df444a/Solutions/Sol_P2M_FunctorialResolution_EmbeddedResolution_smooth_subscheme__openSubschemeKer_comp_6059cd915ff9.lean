-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__openSubschemeKer_comp_6059cd915ff9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:14.189514+00:00
-- url     : https://prove2.me/submissions/ec2488d2-2722-4f82-b676-36f336edb5d8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Theorems.Thm_P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_isIso_openSubschemeKer_subscheme {X : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) :
    ∃ e : W.toScheme ⟶ (openSubschemeKer Z W).subscheme, IsIso e ∧
      e ≫ (openSubschemeKer Z W).subschemeι = Scheme.Opens.ι W ≫ Z.subschemeι := by
  have : IsClosedImmersion (Scheme.Opens.ι W) := W.isClosedImmersion_ι_of_isClosed hW
  have : IsClosedImmersion (Scheme.Opens.ι W ≫ Z.subschemeι) := inferInstance
  have hker : (Scheme.Opens.ι W ≫ Z.subschemeι).ker = (openSubschemeKer Z W).subschemeι.ker :=
    (Scheme.IdealSheafData.ker_subschemeι (openSubschemeKer Z W)).symm
  refine ⟨IsClosedImmersion.lift (openSubschemeKer Z W).subschemeι
      (Scheme.Opens.ι W ≫ Z.subschemeι) (le_of_eq hker.symm), ?_,
    IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (Scheme.Opens.ι W ≫ Z.subschemeι)
    (openSubschemeKer Z W).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hker
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X S : Scheme.{u}} (Z : X.IdealSheafData)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (g : X ⟶ S)
    [Smooth (Z.subschemeι ≫ g)] :
    Smooth ((openSubschemeKer Z W).subschemeι ≫ g) := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_openSubschemeKer_subscheme Z W hW
  have := he
  have hsm : Smooth (Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  have hfac2 : inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g
      = (openSubschemeKer Z W).subschemeι ≫ g := by
    rw [← Category.assoc (Scheme.Opens.ι W) Z.subschemeι g, ← hfac, Category.assoc,
      IsIso.inv_hom_id_assoc]
  have key : Smooth (inv e ≫ Scheme.Opens.ι W ≫ Z.subschemeι ≫ g) := inferInstance
  rwa [hfac2] at key
end FunctorialResolution.EmbeddedResolution
