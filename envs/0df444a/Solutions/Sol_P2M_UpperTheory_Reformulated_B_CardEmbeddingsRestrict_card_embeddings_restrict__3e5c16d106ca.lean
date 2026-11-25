-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_CardEmbeddingsRestrict_card_embeddings_restrict__3e5c16d106ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:09.166451+00:00
-- url     : https://prove2.me/submissions/3c79bd6c-8e1f-4490-8a7e-b0169f8334c5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by
  intro K L _ _ _ _ _ τ
  classical
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [← AlgHom.card K L ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_
  · intro f _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩
  · intro f _ g _ h
    exact AlgHom.ext fun x => RingHom.congr_fun h x
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩
end UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict
