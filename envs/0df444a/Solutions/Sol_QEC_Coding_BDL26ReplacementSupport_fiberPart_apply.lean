-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementSupport.fiberPart_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:16:29.045721+00:00
-- url     : https://prove2.me/submissions/407a3b67-28ca-4850-b680-7001ad1258bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped BigOperators Classical
variable {Label Coordinate : Type} [Fintype Label] [Fintype Coordinate]
  [DecidableEq Label] [DecidableEq Coordinate]
namespace QEC.Coding.BDL26ReplacementSupport
theorem _root_.solution (owner : Coordinate → Label) (label : Label)
    (word : Word Field Coordinate) (coordinate : Coordinate) :
    fiberPart owner label word coordinate =
      if owner coordinate = label then word coordinate else 0 := rfl
end QEC.Coding.BDL26ReplacementSupport
