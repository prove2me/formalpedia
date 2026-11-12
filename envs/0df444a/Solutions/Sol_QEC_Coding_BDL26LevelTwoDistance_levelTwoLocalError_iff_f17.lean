-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.levelTwoLocalError_iff_f17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:02:48.0862+00:00
-- url     : https://prove2.me/submissions/8dfe99ff-b8e0-422b-aa85-11c5e6a7efb1

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (S : OddScale) {depth : Nat}
    (hdepth : 2 ≤ depth)
    (D : MultiscaleDecoder.BDL26DecoderData depth
      (fun _ => (levelTwoPresentation S).X)
      (fun _ => (levelTwoPresentation S).Q)
      (fun _ => (levelTwoPresentation S).Z))
    (error : Word Field (levelTwoPresentation S).Q) :
    levelTwoLocalError S error ↔
      MultiscaleDecoder.LevelTwoLocalError
        (V := fun _ => Vertex (levelOnePresentation S)) D hdepth
        (levelTwoLocalComplex S) error := Iff.rfl
end QEC.Coding.BDL26LevelTwoDistance
