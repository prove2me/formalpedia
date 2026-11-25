-- Prove2me | solution 1 for UpperTheory.V.galois_action_cohomology_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:23.039077+00:00
-- url     : https://prove2.me/submissions/b0f0e5b5-29d5-4c79-b240-5a54db49aa00

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_mul_apply
import Theorems.Thm_UpperTheory_V_galois_action_cohomology_eq_conj

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (τ₁ τ₂ : F ≃+* F) : galoisActionOnCohomology D e (τ₁ * τ₂) = galoisActionOnCohomology D e τ₁ * galoisActionOnCohomology D e τ₂ := by
  obtain ⟨σ₁, h₁⟩ := exists_isLift (Ω := Ω) τ₁
  obtain ⟨σ₂, h₂⟩ := exists_isLift (Ω := Ω) τ₂
  rw [galois_action_cohomology_eq_conj D e h₁, galois_action_cohomology_eq_conj D e h₂, galois_action_cohomology_eq_conj D e (τ := τ₁ * τ₂) (h₂.trans h₁)]
  exact LinearMap.ext fun x => h1TwistConjByLift_mul_apply D e h₂ h₁ _ rfl x
end UpperTheory.V
