-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.emb_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:20.899808+00:00
-- url     : https://prove2.me/submissions/0e60342b-668f-4736-9ea6-0b301b21a8b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Theorems.Thm_PI_SplitIntLoc_Proof_emb_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
variable {v} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F))
    (hp : ∀ a, p (a, a) = a) (f : F) : emb spl p (algebraMap F E f) = algebraMap F (v.adicCompletion F) f := by
  have h : algebraMap F E f ⊗ₜ[F] (1 : (v.adicCompletion F)) = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) f := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [emb_apply, h, hspl, hp]
end PI.SplitIntLoc.Proof
