-- Prove2me | solution 1 for UpperTheory.V.h1TwistConjByLift_eq_self_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:06.675238+00:00
-- url     : https://prove2.me/submissions/9aab146f-8f68-4fbd-9981-9b658c720331

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_conjGS_toGS
import Theorems.Thm_UpperTheory_V_exists_cocycle_h1TwistConjByLift_mk_eq_mk
import Theorems.Thm_UpperTheory_V_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_Gal_mem_Z1_iff_cocycle


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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) (hτ : ∀ x, τ x = x) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  let g₀ : G F Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [h, hτ]
  rw [e₁]
  refine (mk_eq_mk_iff _ _ _).2 ⟨z.1 (toGS Ω _ g₀), fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc : ∀ g k, z.1 (g * k) = z.1 g + qzTw D e g (z.1 k) := ((mem_Z1_iff_cocycle _ z.1).1 z.2).2
  have e1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g₀ * conjGS D h (toGS Ω _ g) = toGS Ω _ g * toGS Ω _ g₀ := by
    rw [conjGS_toGS, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => apply_conjGal h g x
  have e2 := congrArg z.1 e1
  rw [hc, hc, qzTw_apply, chi_toGS] at e2
  have e3 : z₁.1 (toGS Ω _ g) = z.1 (toGS Ω _ g) + qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀) := by
    rw [f₁, ← e2, add_sub_cancel_left]
    rfl
  show z₁.1 (toGS Ω _ g) - z.1 (toGS Ω _ g) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀)
  rw [e3]
  abel
end UpperTheory.V
