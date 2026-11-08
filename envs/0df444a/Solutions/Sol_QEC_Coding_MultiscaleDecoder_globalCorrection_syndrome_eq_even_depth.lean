-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.globalCorrection_syndrome_eq_even_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:51:10.858856+00:00
-- url     : https://prove2.me/submissions/798e8d2a-c206-40a2-8af8-ca838d7ae410

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
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
    {k : Nat}
    {C0 : LevelIndex (2 * k) → Type u}
    {C1 : LevelIndex (2 * k) → Type u}
    {C2 : LevelIndex (2 * k) → Type u}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
    [∀ i, Fintype (C2 i)]
    (D : BDL26DecoderData (2 * k) C0 C1 C2)
    (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D)
    (sigma : D.family.Syndrome (TopIndex (2 * k))) :
    D.family.coboundary1 (TopIndex (2 * k))
        (globalCorrection D S B sigma) =
      (sigma : D.family.Cochain2 (TopIndex (2 * k))) := by
  exact globalCorrection_syndrome_eq D S B sigma
end QEC.Coding.MultiscaleDecoder
