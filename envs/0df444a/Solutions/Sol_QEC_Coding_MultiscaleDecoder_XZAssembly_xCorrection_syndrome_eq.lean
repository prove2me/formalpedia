-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.XZAssembly.xCorrection_syndrome_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:34:54.990856+00:00
-- url     : https://prove2.me/submissions/e8368c79-d2e4-480d-83af-51b69b5ddc21

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
open QEC.Coding.MultiscaleDecoder.XZAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
variable {Z0 Z1 Z2 : LevelIndex depth → Type v}
variable [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)]
namespace QEC.Coding.MultiscaleDecoder.XZAssembly
theorem _root_.solution
    (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth) (A.xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by
  exact globalCorrection_syndrome_eq DX A.xSteps A.xBase sigma
end QEC.Coding.MultiscaleDecoder.XZAssembly
