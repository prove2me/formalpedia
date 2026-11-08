-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2.correctsLocalError_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:49:49.676308+00:00
-- url     : https://prove2.me/submissions/6b3b63d8-2f55-4fb3-8ea1-2670b29630fd

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
open QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2
theorem _root_.solution
    (L : LocalComplexData
      (V (levelTwoIndex hdepth))
      (C2 (levelTwoIndex hdepth))
      (C1 (levelTwoIndex hdepth)))
    (A : F17LevelTwoBaseAdapterV2 D G hdepth)
    (hCorrects : A.CorrectsLocalErrors L)
    (I : LevelTwoSmallErrorInputV2 D hdepth)
    (hLocal : I.IsLocal L) :
    I.error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier :=
  hCorrects I hLocal
end QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapterV2
