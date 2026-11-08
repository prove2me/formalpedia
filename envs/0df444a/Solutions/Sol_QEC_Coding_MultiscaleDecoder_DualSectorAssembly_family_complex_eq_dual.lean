-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.DualSectorAssembly.family_complex_eq_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:52:45.755277+00:00
-- url     : https://prove2.me/submissions/6fe45075-3876-4fa9-8284-5649ab6af03c

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
open QEC.Coding.MultiscaleDecoder.DualSectorAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
namespace QEC.Coding.MultiscaleDecoder.DualSectorAssembly
theorem _root_.solution
    (A : DualSectorAssembly DX) (i : LevelIndex depth) :
    A.DZ.family.complex i = dualChainComplex (DX.family.complex i) := by
  rw [A.family_eq_dual]
  rfl
end QEC.Coding.MultiscaleDecoder.DualSectorAssembly
