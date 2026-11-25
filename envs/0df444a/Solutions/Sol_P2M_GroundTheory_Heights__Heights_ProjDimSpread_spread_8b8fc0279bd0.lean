-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:44.135432+00:00
-- url     : https://prove2.me/submissions/b5bcad4c-8a31-450f-a1e4-f88df5d3a399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open CategoryTheory
variable {R : Type} [CommRing R]
namespace GroundTheory.Heights₂.Heights
namespace ProjDimSpread
theorem _root_.solution [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) [Module.Finite R M],
      HasProjectiveDimensionLE (M.localizedModule P.primeCompl) n →
      ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
        HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) n := by
  induction n with
  | zero => exact fun M _ h ↦ spread_zero P M h
  | succ n ih =>
    intro M _ h
    rcases Module.exists_finite_presentation R M with ⟨F, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have Sp_exact (T : Submonoid R) : (S.map (ModuleCat.localizedModuleFunctor T)).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor T)
    have projp (T : Submonoid R) : Projective (S.map (ModuleCat.localizedModuleFunctor T)).X₂ :=
      (ModuleCat.localizedModuleFunctor.{0} T).projective_obj_of_projective proj
    have hK : HasProjectiveDimensionLE
        ((ModuleCat.of R (LinearMap.ker f)).localizedModule P.primeCompl) n :=
      ((Sp_exact P.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mp h
    obtain ⟨g, hg, hQ⟩ := ih (ModuleCat.of R (LinearMap.ker f)) hK
    exact ⟨g, hg, fun Q _ hgQ ↦
      ((Sp_exact Q.primeCompl).hasProjectiveDimensionLT_X₃_iff n (projp _)).mpr (hQ Q hgQ)⟩
end ProjDimSpread
end GroundTheory.Heights₂.Heights
