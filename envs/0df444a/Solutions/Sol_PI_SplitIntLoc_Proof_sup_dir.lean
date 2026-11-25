-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.sup_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:10.656447+00:00
-- url     : https://prove2.me/submissions/839947d7-0db0-450b-91e1-0f3fcd20e049

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_exists_unit_diff
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
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (h1 : (spl x).1 ∈ (v.adicCompletionIntegers F)) (h2 : (spl x).2 ∈ (v.adicCompletionIntegers F)) :
    x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := by
  obtain ⟨b, hb⟩ := exists_unit_diff spl hspl
  obtain ⟨u, hu⟩ := hb.exists_right_inv
  have hu' : ((phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F)) - (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) *
      (u : (v.adicCompletion F)) = 1 := congrArg Subtype.val hu
  have hE : ∀ e : 𝓞 E, (algebraMap (𝓞 E) E e) ⊗ₜ[F] (1 : (v.adicCompletion F)) ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := fun e =>
    Subring.subset_closure (Or.inl ⟨⟨_, RingHom.mem_range.2 ⟨e, rfl⟩⟩, rfl⟩)
  have hK : ∀ c : (v.adicCompletionIntegers F), (1 : E) ⊗ₜ[F] (c : (v.adicCompletion F)) ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := fun c =>
    Subring.subset_closure (Or.inr ⟨⟨c, c.2⟩, rfl⟩)
  obtain ⟨w, hw_def⟩ : ∃ w : E ⊗[F] (v.adicCompletion F), w = (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : (v.adicCompletion F)) -
      (1 : E) ⊗ₜ[F] (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) * ((1 : E) ⊗ₜ[F] (u : (v.adicCompletion F))) := ⟨_, rfl⟩
  have hw : w ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := by
    rw [hw_def]
    exact Subring.mul_mem _ (Subring.sub_mem _ (hE b) (hK _)) (hK u)
  have hsw : spl w = (1, 0) := by
    rw [hw_def, map_mul, map_sub, spl_tmul_one, hspl, hspl]
    refine Prod.ext ?_ ?_
    · exact hu'
    · show ((phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F)) - (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) *
        (u : (v.adicCompletion F)) = 0
      rw [sub_self, zero_mul]
  have hx' : spl x = spl ((1 : E) ⊗ₜ[F] (((⟨_, h2⟩ : (v.adicCompletionIntegers F))) : (v.adicCompletion F)) +
      w * ((1 : E) ⊗ₜ[F] ((((⟨_, h1⟩ : (v.adicCompletionIntegers F)) - ⟨_, h2⟩ : (v.adicCompletionIntegers F))) : (v.adicCompletion F)))) := by
    rw [map_add, map_mul, hsw, hspl, hspl]
    refine Prod.ext ?_ ?_
    · show (spl x).1 = (spl x).2 + 1 * ((spl x).1 - (spl x).2)
      ring
    · show (spl x).2 = (spl x).2 + 0 * ((spl x).1 - (spl x).2)
      ring
  rw [spl.injective hx']
  exact Subring.add_mem _ (hK _) (Subring.mul_mem _ hw (hK _))
end PI.SplitIntLoc.Proof
