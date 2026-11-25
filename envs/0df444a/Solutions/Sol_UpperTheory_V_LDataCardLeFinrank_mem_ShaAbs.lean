-- Prove2me | solution 1 for UpperTheory.V.LDataCardLeFinrank.mem_ShaAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:00:17.210409+00:00
-- url     : https://prove2.me/submissions/8ed414cf-f7ae-4acf-a480-90a15b28860c

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
namespace UpperTheory.V.LDataCardLeFinrank
theorem _root_.solution (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (x : H1 ρ) :
    x ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val x = 0) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val x = 0 := by
  simp only [ShaAbs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
end UpperTheory.V.LDataCardLeFinrank
