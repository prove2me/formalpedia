-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.mem_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:33.037886+00:00
-- url     : https://prove2.me/submissions/9e3b3ede-0548-44b4-88f3-0f7cec9d735d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Theorems.Thm_PI_SplitIntLoc_Proof_mem_max_iff

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
theorem _root_.solution (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (z : 𝓞 E) :
    z ∈ P spl p ↔ Valued.v (emb spl p (algebraMap (𝓞 E) E z)) < 1 := by
  rw [P, Ideal.mem_comap, mem_max_iff]
  exact Iff.rfl
end PI.SplitIntLoc.Proof
