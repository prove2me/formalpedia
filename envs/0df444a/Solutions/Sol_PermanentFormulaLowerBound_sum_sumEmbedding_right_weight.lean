-- Prove2me | solution 1 for PermanentFormulaLowerBound.sum_sumEmbedding_right_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/f6cb3822-872b-462b-bcf5-c17d07313f0f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_sum_sumEmbedding_left_weight

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
    (w : (β ↪ γ) → F) :
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inr.trans rho)) =
        ((Fintype.card γ - Fintype.card β).descFactorial
          (Fintype.card α) : F) *
          ∑ rho : (β ↪ γ), w rho := by
  classical
  calc
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inr.trans rho)) =
        ∑ rho : (β ⊕ α ↪ γ),
          w (Function.Embedding.inl.trans rho) := by
            refine Fintype.sum_equiv
              (Equiv.embeddingCongr (Equiv.sumComm α β)
                (Equiv.refl γ)) _ _ ?_
            intro rho
            apply congrArg w
            apply Function.Embedding.ext
            intro b
            rfl
    _ = ((Fintype.card γ - Fintype.card β).descFactorial
          (Fintype.card α) : F) *
          ∑ rho : (β ↪ γ), w rho :=
        sum_sumEmbedding_left_weight w
end PermanentFormulaLowerBound
