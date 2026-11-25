-- Prove2me | solution 1 for UpperTheory.V.galois_action_cohomology_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:20:56.803957+00:00
-- url     : https://prove2.me/submissions/78173c79-fe01-4e22-af32-58a6c6c03c62

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_eq_of_isLift_of_isLift

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) : galoisActionOnCohomology D e τ = h1TwistConjByLift D e h :=
  h1TwistConjByLift_eq_of_isLift_of_isLift D e _ h
end UpperTheory.V
