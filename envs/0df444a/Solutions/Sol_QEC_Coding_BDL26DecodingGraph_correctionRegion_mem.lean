-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.correctionRegion_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:13:16.054744+00:00
-- url     : https://prove2.me/submissions/387a0bb1-36c3-4641-8fcd-09bc3f98cd00

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_mem_radius_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
namespace QEC.Coding.BDL26DecodingGraph
theorem _root_.solution (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (correctionRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true :=
  mem_radius_one S n u v
end QEC.Coding.BDL26DecodingGraph
