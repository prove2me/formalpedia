-- Prove2me | solution 1 for PermanentFormulaLowerBound.sum_sumEmbedding_left_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/01f0550a-a6c7-4f4f-be4d-718a634d8d7f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F α β γ : Type*} [CommSemiring F]
    [Fintype α] [Fintype β] [Fintype γ]
    (w : (α ↪ γ) → F) :
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inl.trans rho)) =
        ((Fintype.card γ - Fintype.card α).descFactorial
          (Fintype.card β) : F) *
          ∑ rho : (α ↪ γ), w rho := by
  classical
  calc
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inl.trans rho)) =
        ∑ z : (Σ rho : (α ↪ γ), β ↪ ↥(Set.range rho)ᶜ), w z.1 := by
          refine Fintype.sum_equiv
            (Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted
              (α := α) (β := β) (γ := γ)) _ _ ?_
          intro rho
          rfl
    _ = ∑ rho : (α ↪ γ),
          ∑ _eta : (β ↪ ↥(Set.range rho)ᶜ), w rho :=
        Fintype.sum_sigma _
    _ = ∑ rho : (α ↪ γ),
          ((Fintype.card γ - Fintype.card α).descFactorial
            (Fintype.card β) : F) * w rho := by
        apply Finset.sum_congr rfl
        intro rho _
        have hcard :
            Fintype.card (↥(Set.range rho)ᶜ) =
              Fintype.card γ - Fintype.card α := by
          rw [Fintype.card_compl_set, Fintype.card_range]
        simp [Fintype.card_embedding_eq, hcard, nsmul_eq_mul]
    _ = ((Fintype.card γ - Fintype.card α).descFactorial
          (Fintype.card β) : F) *
          ∑ rho : (α ↪ γ), w rho := by
        rw [Finset.mul_sum]
end PermanentFormulaLowerBound
