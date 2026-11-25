-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.prime_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:01.926126+00:00
-- url     : https://prove2.me/submissions/9bef131c-d9c7-4b7e-bafc-0b7c3de5312b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Theorems.Thm_PI_SplitIntLoc_Proof_exists_unif
import Theorems.Thm_PI_SplitIntLoc_Proof_emb_algebraMap
import Theorems.Thm_PI_SplitIntLoc_Proof_mem_P

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
    (hp : ∀ a, p (a, a) = a) : P spl p ≠ ⊥ := by
  obtain ⟨π, hπ0, hπ⟩ := exists_unif v
  intro hbot
  have hmem : algebraMap (𝓞 F) (𝓞 E) π ∈ P spl p := by
    rw [mem_P, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
      emb_algebraMap spl hspl p hp]
    exact hπ
  rw [hbot, Ideal.mem_bot] at hmem
  apply hπ0
  have := congrArg (algebraMap (𝓞 E) E) hmem
  rw [map_zero, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  exact (map_eq_zero_iff _ (algebraMap F E).injective).1 this
end PI.SplitIntLoc.Proof
