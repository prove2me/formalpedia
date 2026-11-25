-- Prove2me | solution 1 for UpperTheory.V.galois_action_preserves_sha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:57.76641+00:00
-- url     : https://prove2.me/submissions/746eb36a-dd46-4f28-ac94-bc3239cb0c32

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_mem_sha_of_mem_sha

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
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    galoisActionOnCohomology D e τ x ∈ Sha D e :=
  h1TwistConjByLift_mem_sha_of_mem_sha D e _ hx
end UpperTheory.V
