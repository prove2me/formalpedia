-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.tannerLevel_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:53:49.319573+00:00
-- url     : https://prove2.me/submissions/f32e076c-e43c-42f7-bb3d-129c10aef8b9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
namespace QEC.Coding.BDL26DecodingGraph
theorem _root_.solution (P : TannerSquarePresentation) :
    LevelGraphDirectedOrientation (tannerLevel P) :=
  (tannerLevel P).directedEdge_orientation
end QEC.Coding.BDL26DecodingGraph
