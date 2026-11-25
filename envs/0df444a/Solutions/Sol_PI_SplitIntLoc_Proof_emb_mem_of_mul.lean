-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.emb_mem_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:30.468538+00:00
-- url     : https://prove2.me/submissions/5dfb8f70-6c7b-4ff5-8cf1-3b767f656dca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_coe_phi


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
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (a s : 𝓞 E) (hs : s ∉ P spl p) (z : E)
    (hz : z * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a) : emb spl p z ∈ (v.adicCompletionIntegers F) := by
  have hu : IsUnit (phi spl p s) := by
    by_contra h
    apply hs
    show phi spl p s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
    rw [IsLocalRing.mem_maximalIdeal]
    exact h
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 : (phi spl p s : (v.adicCompletion F)) * (w : (v.adicCompletion F)) = 1 := congrArg Subtype.val hw
  have h3 : emb spl p z = (phi spl p a : (v.adicCompletion F)) * (w : (v.adicCompletion F)) := by
    rw [coe_phi, ← hz, map_mul, ← coe_phi, mul_assoc, h2, mul_one]
  rw [h3]
  exact (phi spl p a * w).2
end PI.SplitIntLoc.Proof
