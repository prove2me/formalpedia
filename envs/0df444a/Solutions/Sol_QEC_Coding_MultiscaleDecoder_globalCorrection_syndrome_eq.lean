-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.globalCorrection_syndrome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:31:37.348911+00:00
-- url     : https://prove2.me/submissions/c4eb9347-ce83-4587-90f9-28fc0c837dd3

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_globalCorrection_eq_input

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
    D.family.coboundary1 (TopIndex depth) (globalCorrection D S B sigma) =
      (sigma : D.family.Cochain2 (TopIndex depth)) := by
  exact globalCorrection_eq_input D S B sigma
end QEC.Coding.MultiscaleDecoder
