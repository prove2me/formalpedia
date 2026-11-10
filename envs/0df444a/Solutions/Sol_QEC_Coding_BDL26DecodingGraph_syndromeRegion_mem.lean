-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.syndromeRegion_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:15:09.701605+00:00
-- url     : https://prove2.me/submissions/f63c5162-4d2e-471f-9847-8b9c04e505e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_mem_radius_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
namespace QEC.Coding.BDL26DecodingGraph
theorem _root_.solution (S : OddScale) (n : Nat)
    (u v : Vertex (state S n).presentation) :
    u ∈ (syndromeRegion S n v).vertices ↔
      u = v ∨ tannerDirected (state S n).presentation u v = true ∨
        ∃ w : Vertex (state S n).presentation,
          tannerDirected (state S n).presentation u w = true ∧
          tannerDirected (state S n).presentation w v = true :=
  mem_radius_two S n u v
end QEC.Coding.BDL26DecodingGraph
