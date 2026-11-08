-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_base_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:28:02.78021+00:00
-- url     : https://prove2.me/submissions/86a10e4c-3f97-403d-9bb4-05c1147ab650

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_base_readout
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_terminalInput_alternating_weight

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
    (B : AuditedBaseDecoder D)
    (hstep : ∀ (i : StepIndex depth) (s : D.family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val
      else HammingWeight (S.step i s).coarse.val ≤ HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    2 ^ ((depth + 1) / 2) *
      HammingWeight (historyInputReadout D (buildCorrectionHistory D S B sigma) 0) ≤
        HammingWeight sigma.val := by
  rw [buildCorrectionHistory_base_readout]
  exact terminalInput_alternating_weight D S hstep sigma
end QEC.Coding.MultiscaleDecoder
