-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_base_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:22:51.416363+00:00
-- url     : https://prove2.me/submissions/71b9c74f-b68d-4109-8871-fb3af9988555

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
namespace QEC.Coding.MultiscaleDecoder
theorem _root_.solution
    (D : BDL26DecoderData depth C0 C1 C2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex depth)) :
    historyInputReadout D (buildCorrectionHistory D S B sigma) 0 =
      (terminalInput D S sigma).val := by
  have aux : ∀ (n : Nat) (hn : n ≤ depth)
      (s : D.family.Syndrome ⟨n, Nat.lt_succ_of_le hn⟩),
      historyInputReadout D (buildHistoryAux D S B n hn s) 0 =
        (terminalInputAux D S n hn s).val := by
    intro n
    induction n with
    | zero =>
        intro hn s
        rw [buildHistoryAux, terminalInputAux]
        exact historyInputReadout_base D _
    | succ n ih =>
        intro hn s
        rw [buildHistoryAux, terminalInputAux]
        change historyInputReadout D (.step _ _ :: buildHistoryAux D S B n _ _) 0 = _
        rw [historyInputReadout_step_zero]
        exact ih _ _
  exact aux depth (Nat.le_refl _) sigma
end QEC.Coding.MultiscaleDecoder
