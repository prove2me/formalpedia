-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:26.93381+00:00
-- url     : https://prove2.me/submissions/af6b6914-b535-48aa-899b-1ad013181e41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_spl_tmul
import Theorems.Thm_PI_SplitIntLoc_Proof_exists_small
import Theorems.Thm_PI_SplitIntLoc_Proof_emb_algebraMap


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
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (z : E ⊗[F] (v.adicCompletion F)) :
    ∃ y : E, Valued.v ((spl z).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) < 1 ∧
      Valued.v ((spl z).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) < 1 := by
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_small (v := v)
  have key : ∀ w : (v.adicCompletion F), w ∈ (v.adicCompletionIntegers F) → Valued.v (ϖ * w) < 1 := fun w hw =>
    have hw' : Valued.v w ≤ 1 := hw
    calc Valued.v (ϖ * w) = Valued.v ϖ * Valued.v w := map_mul _ _ _
      _ ≤ Valued.v ϖ * 1 := by gcongr
      _ = Valued.v ϖ := mul_one _
      _ < 1 := hϖ
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul e a =>
    let U : Set (v.adicCompletion F) :=
      (fun x => ϖ⁻¹ * emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e * (a - x)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F)) ∩
      (fun x => ϖ⁻¹ * emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e * (a - x)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))
    have hU : IsOpen U := by
      refine IsOpen.inter ?_ ?_ <;>
      exact (Valued.isOpen_integer (v.adicCompletion F)).preimage
        (continuous_const.mul (continuous_const.sub continuous_id))
    have hU' : U.Nonempty := ⟨a, by
      simp only [U, Set.mem_inter_iff, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
      exact ⟨zero_mem _, zero_mem _⟩⟩
    obtain ⟨f, hf⟩ := (denseRange_algebraMap F v).exists_mem_open hU hU'
    have hsmall : ∀ c : (v.adicCompletion F), ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f) ∈ (v.adicCompletionIntegers F) →
        Valued.v (c * a - algebraMap F (v.adicCompletion F) f * c) < 1 := fun c hc => by
      have h : c * a - algebraMap F (v.adicCompletion F) f * c = ϖ * (ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f)) := by
        rw [show ϖ * (ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f)) =
          (ϖ * ϖ⁻¹) * (c * (a - algebraMap F (v.adicCompletion F) f)) by ring, mul_inv_cancel₀ hϖ0, one_mul]
        ring
      rw [h]
      exact key _ hc
    refine ⟨algebraMap F E f * e, ?_, ?_⟩
    · rw [spl_tmul spl hspl, map_mul, emb_algebraMap spl hspl _ (fun _ => rfl)]
      exact hsmall _ hf.1
    · rw [spl_tmul spl hspl, map_mul, emb_algebraMap spl hspl _ (fun _ => rfl)]
      exact hsmall _ hf.2
  | add x y hx hy =>
    obtain ⟨y1, h1, h1'⟩ := hx
    obtain ⟨y2, h2, h2'⟩ := hy
    refine ⟨y1 + y2, ?_, ?_⟩
    · rw [map_add, map_add, Prod.fst_add,
        show (spl x).1 + (spl y).1 - (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y1 + emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y2)
          = ((spl x).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y1) + ((spl y).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y2)
          by ring]
      exact Valuation.map_add_lt _ h1 h2
    · rw [map_add, map_add, Prod.snd_add,
        show (spl x).2 + (spl y).2 - (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y1 + emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y2)
          = ((spl x).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y1) + ((spl y).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y2)
          by ring]
      exact Valuation.map_add_lt _ h1' h2'
end PI.SplitIntLoc.Proof
