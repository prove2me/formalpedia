-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.sub_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:17.216561+00:00
-- url     : https://prove2.me/submissions/7c8fa378-9888-4f69-a514-71ecc0e180f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Theorems.Thm_PI_SplitIntLoc_Proof_spl_tmul_one

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
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring) :
    (spl x).1 ∈ (v.adicCompletionIntegers F) ∧ (spl x).2 ∈ (v.adicCompletionIntegers F) := by
  let S : Subring (E ⊗[F] (v.adicCompletion F)) :=
    (((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring).comap (spl : E ⊗[F] (v.adicCompletion F) →+* (v.adicCompletion F) × (v.adicCompletion F))
  have hS : tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 he
      have hz : IsIntegral ℤ (algebraMap (𝓞 E) E z) := RingOfIntegers.isIntegral_coe z
      show spl (algebraMap (𝓞 E) E z ⊗ₜ[F] 1) ∈
        ((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring
      rw [spl_tmul_one, Subring.mem_prod]
      exact ⟨emb_mem_of_isIntegral spl (RingHom.fst _ _) _ hz,
        emb_mem_of_isIntegral spl (RingHom.snd _ _) _ hz⟩
    · show spl ((1 : E) ⊗ₜ[F] y) ∈
        ((v.adicCompletionIntegers F)).toSubring.prod ((v.adicCompletionIntegers F)).toSubring
      rw [Subring.mem_prod, hspl]
      exact ⟨hy, hy⟩
  exact Subring.mem_prod.1 (hS hx)
end PI.SplitIntLoc.Proof
