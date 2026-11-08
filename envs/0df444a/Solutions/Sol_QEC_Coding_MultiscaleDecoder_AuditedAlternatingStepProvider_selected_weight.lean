-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider.selected_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:50:05.687033+00:00
-- url     : https://prove2.me/submissions/1b53a00e-b60d-4ae9-a9d0-83511cf1c307

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
open QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider
variable {D : BDL26DecoderData depth C0 C1 C2}
namespace QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider
theorem _root_.solution
    (P : AuditedAlternatingStepProvider D)
    (i : StepIndex depth) (sigma : D.family.Syndrome i.succ) :
    (i.succ.val % 2 = 1 ∧
      2 * HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) ∨
    (i.succ.val % 2 ≠ 1 ∧
      HammingWeight ((P.selected i sigma).coarse : D.family.Cochain2 i.castSucc) ≤
        HammingWeight (sigma : D.family.Cochain2 i.succ)) := by
  by_cases h : i.succ.val % 2 = 1
  · left
    refine ⟨h, ?_⟩
    rw [selected, dif_pos h]
    exact P.rxWeight i h sigma
  · right
    have hEven := even_of_not_odd h
    refine ⟨h, ?_⟩
    rw [selected, dif_neg h]
    exact P.rzWeight i hEven sigma
end QEC.Coding.MultiscaleDecoder.AuditedAlternatingStepProvider
