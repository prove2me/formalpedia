-- Prove2me | solution 1 for UpperTheory.V.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:50.545811+00:00
-- url     : https://prove2.me/submissions/9f296e03-6b11-43d4-812d-e534d5a3c50a

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (z z' : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) = Submodule.Quotient.mk z' ↔ ∃ m, ∀ g, z.1 g - z'.1 g = ρ g m - m := by
  refine (Submodule.Quotient.eq _).trans ((mem_coboundaries1 _ _).trans ?_)
  first
    | exact Iff.rfl
    | exact ⟨fun ⟨m, hm⟩ => ⟨m, fun g => (hm g).symm⟩, fun ⟨m, hm⟩ => ⟨m, fun g => (hm g).symm⟩⟩
end UpperTheory.V
