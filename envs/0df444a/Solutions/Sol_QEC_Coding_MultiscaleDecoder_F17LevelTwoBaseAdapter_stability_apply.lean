-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter.stability_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:49:45.432434+00:00
-- url     : https://prove2.me/submissions/254a70f5-091c-4d9c-aa0c-46cb4e1c1fc8

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
open QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter
variable {V : LevelIndex depth → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {G : DecodingGraphFamily depth V}
variable {hdepth : 2 ≤ depth}
namespace QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter
theorem _root_.solution
    (A : F17LevelTwoBaseAdapter D G hdepth)
    (I : StabilityBaseLevelTwoInput D G hdepth)
    (error : D.family.Correction (levelTwoIndex hdepth))
    (hfit : I.supportFitsRadiusTwo)
    (hsyndrome : (I.syndrome : D.family.Cochain2 (levelTwoIndex hdepth)) =
      D.family.coboundary1 (levelTwoIndex hdepth) error) :
    error + A.decode I.syndrome ∈
      (D.family.complex (levelTwoIndex hdepth)).firstCoboundaryCheckCode.carrier :=
  A.stability I error hfit hsyndrome
end QEC.Coding.MultiscaleDecoder.F17LevelTwoBaseAdapter
