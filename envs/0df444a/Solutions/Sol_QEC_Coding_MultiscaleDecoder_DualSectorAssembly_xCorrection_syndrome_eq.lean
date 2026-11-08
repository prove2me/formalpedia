-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.DualSectorAssembly.xCorrection_syndrome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:52:57.117915+00:00
-- url     : https://prove2.me/submissions/4c79e090-701c-442c-8e93-23e0ecaf7cc2

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_XZAssembly_xCorrection_syndrome_eq

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
open QEC.Coding.MultiscaleDecoder.DualSectorAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
namespace QEC.Coding.MultiscaleDecoder.DualSectorAssembly
theorem _root_.solution
    (A : DualSectorAssembly DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth)
        ((A.toXZAssembly).xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by
  exact XZAssembly.xCorrection_syndrome_eq A.toXZAssembly sigma
end QEC.Coding.MultiscaleDecoder.DualSectorAssembly
