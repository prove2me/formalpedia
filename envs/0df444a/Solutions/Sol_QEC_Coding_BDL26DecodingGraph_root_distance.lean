-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.root_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:02:30.62813+00:00
-- url     : https://prove2.me/submissions/47e26a74-049d-408b-9fa4-fda371b3baa4

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
theorem _root_.solution : rootLevel.graph.distance () () = (0 : WithTop Nat) := by
  decide
end QEC.Coding.BDL26DecodingGraph
