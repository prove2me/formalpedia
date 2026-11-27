-- Prove2me | solution 1 for UpperTheory.V.LDataCardLeFinrank.mk_mem_ShaAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:02.267374+00:00
-- url     : https://prove2.me/submissions/6d85268b-f984-4ea7-bde8-6f3d194b2adb

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_mem_ShaAbs
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


section
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
namespace UpperTheory.V.LDataCardLeFinrank
section
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
variable {F l}
end
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
private theorem resH1_mk_eq_zero_iff_coboundary (ρ : Representation R (G F Ω) M) (z : Z1 ρ) (H : Subgroup (G F Ω)) :
    resH1 ρ H.subtype continuous_subtype_val (Submodule.Quotient.mk z) = 0 ↔
      ∃ m, ∀ g ∈ H, z.1 g = ρ g m - m := by
  simp [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_coboundaries1, restrictCocycles1]
end
end UpperTheory.V.LDataCardLeFinrank
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
namespace UpperTheory.V.LDataCardLeFinrank
theorem _root_.solution (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Dec (F := F) A, z.1 g = ρ g m - m) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Ine (F := F) A, z.1 g = ρ g m - m := by
  simp only [mem_ShaAbs, resH1_mk_eq_zero_iff_coboundary]
end UpperTheory.V.LDataCardLeFinrank
