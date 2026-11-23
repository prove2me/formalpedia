-- Prove2me | solution 1 for UpperTheory.V.h1TwistConjByLift_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.821323+00:00
-- url     : https://prove2.me/submissions/1ab7077a-0f14-4148-8069-1ce6d5644d50

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_conjGS_toGS
import Theorems.Thm_UpperTheory_V_exists_cocycle_h1TwistConjByLift_mk_eq_mk

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) {τ₁ τ₂ τ₃ : F ≃+* F} {σ₁ σ₂ σ₃ : Ω ≃+* Ω} (h₁ : IsLift τ₁ σ₁)
    (h₂ : IsLift τ₂ σ₂) (h₃ : IsLift τ₃ σ₃) (hσ : σ₃ = σ₂ * σ₁) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h₃ x = h1TwistConjByLift D e h₂ (h1TwistConjByLift D e h₁ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₁ z
  obtain ⟨z₂, e₂, f₂⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₂ z₁
  obtain ⟨z₃, e₃, f₃⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₃ z
  rw [e₁, e₂, e₃]
  congr 1
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have e4 : conjGS D h₃ (toGS Ω _ g) = conjGS D h₁ (conjGS D h₂ (toGS Ω _ g)) := by
    rw [conjGS_toGS, conjGS_toGS, conjGS_toGS]
    congr 1
    subst hσ
    rfl
  refine (f₃ _).trans (Eq.trans ?_ (f₂ _).symm)
  rw [f₁, smul_smul]
  refine congrArg₂ (· • ·) ?_ (congrArg z.1 e4)
  rw [twScal, twScal, twScal, hσ, map_mul, mul_zpow, Units.val_mul]
end UpperTheory.V
