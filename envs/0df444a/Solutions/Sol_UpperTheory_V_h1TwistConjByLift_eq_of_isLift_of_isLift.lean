-- Prove2me | solution 1 for UpperTheory.V.h1TwistConjByLift_eq_of_isLift_of_isLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:25.794433+00:00
-- url     : https://prove2.me/submissions/3643abdc-d741-4c2e-8f68-1d6e60d05e87

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_mul_apply
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_eq_self_of_forall_apply_eq

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) {σ' : Ω ≃+* Ω} (h : IsLift τ σ) (h' : IsLift τ σ') :
    h1TwistConjByLift D e h = h1TwistConjByLift D e h' := by
  refine LinearMap.ext fun x => ?_
  rw [h1TwistConjByLift_mul_apply D e (h.trans h'.symm) h' h (RingEquiv.ext fun y => (σ'.apply_symm_apply _).symm),
    h1TwistConjByLift_eq_self_of_forall_apply_eq D e (h.trans h'.symm) fun y => τ.symm_apply_apply y]
end UpperTheory.V
