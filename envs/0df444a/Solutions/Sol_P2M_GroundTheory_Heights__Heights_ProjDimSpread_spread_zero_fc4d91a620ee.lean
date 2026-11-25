-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_zero_fc4d91a620ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:50.29346+00:00
-- url     : https://prove2.me/submissions/28235311-f509-4024-935a-8662f3241513

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b

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
theorem _root_.solution [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{0} R) [Module.Finite R M]
    (h : HasProjectiveDimensionLE (M.localizedModule P.primeCompl) 0) :
    ∃ g : R, g ∉ P ∧ ∀ (Q : Ideal R) [Q.IsPrime], g ∉ Q →
      HasProjectiveDimensionLE (M.localizedModule Q.primeCompl) 0 := by
  rw [hasProjectiveDimensionLE_zero_iff] at h
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.Flat.of_projective
  have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  have hP : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M :=
    Module.mem_freeLocus.mpr hfree
  obtain ⟨_, ⟨g, rfl⟩, hPg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP
      Module.isOpen_freeLocus
  refine ⟨g, (PrimeSpectrum.mem_basicOpen g _).mp hPg, fun Q _ hQ ↦ ?_⟩
  have : Module.Free (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) :=
    Module.mem_freeLocus.mp (hsub ((PrimeSpectrum.mem_basicOpen g ⟨Q, inferInstance⟩).mpr hQ))
  exact (hasProjectiveDimensionLE_zero_iff M Q.primeCompl).mpr Module.Projective.of_free
end ProjDimSpread
end GroundTheory.Heights₂.Heights
