-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.DualSectorAssembly.zCorrection_syndrome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:52:59.031929+00:00
-- url     : https://prove2.me/submissions/d58f6281-1e68-49b8-8c59-09cffc483ee1

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_XZAssembly_zCorrection_syndrome_eq

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
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.coboundary1 (TopIndex depth)
        ((A.toXZAssembly).zCorrection sigma) =
      (sigma : A.DZ.family.Cochain2 (TopIndex depth)) := by
  exact XZAssembly.zCorrection_syndrome_eq A.toXZAssembly sigma
end QEC.Coding.MultiscaleDecoder.DualSectorAssembly
