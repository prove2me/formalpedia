-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_ker_subscheme__comp_eq_of_ker_le_9ee7054b5bee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:49:00.891423+00:00
-- url     : https://prove2.me/submissions/edcdf022-8bbd-4653-90bd-ae3cc7fc335c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_ker_of_isIso_comp

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
private theorem comap_eq_ker_of_mono {U V : Scheme.{u}} (j : U ⟶ V) [Mono j]
    (I : V.IdealSheafData) (lam : I.subscheme ⟶ U) (hlam : lam ≫ j = I.subschemeι) :
    I.comap j = Scheme.Hom.ker lam := by
  have hc : I.comap j = Scheme.Hom.ker (Limits.pullback.fst j I.subschemeι) := rfl
  have hcomm : lam ≫ j = 𝟙 I.subscheme ≫ I.subschemeι := by rw [hlam, Category.id_comp]
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : I.subscheme ⟶ Limits.pullback j I.subschemeι,
      e ≫ Limits.pullback.fst j I.subschemeι = lam ∧
        e ≫ Limits.pullback.snd j I.subschemeι = 𝟙 I.subscheme :=
    ⟨Limits.pullback.lift lam (𝟙 I.subscheme) hcomm, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  have hsndlam : Limits.pullback.snd j I.subschemeι ≫ lam
      = Limits.pullback.fst j I.subschemeι := by
    rw [← cancel_mono j, Category.assoc, hlam, ← Limits.pullback.condition]
  have : IsIso e := by
    refine ⟨Limits.pullback.snd j I.subschemeι, hesnd, ?_⟩
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, hsndlam, Category.id_comp]
    · rw [Category.assoc, hesnd, Category.comp_id, Category.id_comp]
  rw [hc]
  exact (ker_eq_ker_of_isIso_comp lam (Limits.pullback.fst j I.subschemeι) e hefst).symm
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {U V : Scheme.{u}} (j : U ⟶ V) [IsClosedImmersion j]
    (L : V.IdealSheafData) (hL : Scheme.Hom.ker j ≤ L) (K : U.IdealSheafData)
    (hK : K = L.comap j) :
    Scheme.Hom.ker (K.subschemeι ≫ j) = L := by
  have hle : Scheme.Hom.ker j ≤ Scheme.Hom.ker L.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hL
  have hfac : IsClosedImmersion.lift j L.subschemeι hle ≫ j = L.subschemeι := by
    rw [IsClosedImmersion.lift_fac]
  have hcomap : L.comap j = Scheme.Hom.ker (IsClosedImmersion.lift j L.subschemeι hle) :=
    comap_eq_ker_of_mono j L (IsClosedImmersion.lift j L.subschemeι hle) hfac
  rw [hK, hcomap, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.Hom.ker_comp, hfac, Scheme.IdealSheafData.ker_subschemeι]
end FunctorialResolution.EmbeddedResolution
