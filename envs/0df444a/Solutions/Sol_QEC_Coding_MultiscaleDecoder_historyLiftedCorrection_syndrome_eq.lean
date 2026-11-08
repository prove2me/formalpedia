-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.historyLiftedCorrection_syndrome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:34:25.835668+00:00
-- url     : https://prove2.me/submissions/5be58ec0-3b8d-44e8-a4eb-044295ecde12

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historyLiftedCorrection_eq_globalCorrection
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_globalCorrection_syndrome_eq

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
    (D : BDL26DecoderData depth C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex depth)) :
    D.family.coboundary1 (TopIndex depth)
        (historyLiftedCorrection D (buildCorrectionHistory D S B sigma)) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by
  rw [historyLiftedCorrection_eq_globalCorrection D S B sigma]
  exact globalCorrection_syndrome_eq D S B sigma
end QEC.Coding.MultiscaleDecoder
