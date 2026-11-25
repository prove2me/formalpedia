-- Prove2me | solution 1 for UpperTheory.V.galois_action_cohomology_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:15.660322+00:00
-- url     : https://prove2.me/submissions/a0959a84-fb92-493c-bc36-a6aefe99ebac

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) : galoisActionOnCohomology D e (1 : F ≃+* F) = 1 :=
  LinearMap.ext fun x => h1TwistConjByLift_eq_self_of_forall_apply_eq D e _ (fun _ => rfl) x
end UpperTheory.V
