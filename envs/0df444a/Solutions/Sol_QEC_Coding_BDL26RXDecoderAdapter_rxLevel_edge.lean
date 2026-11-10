-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.rxLevel_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:53:16.147371+00:00
-- url     : https://prove2.me/submissions/14b42aba-959d-43e4-aed0-0b0b9be06be7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (u v) :
    (rxLevel P).graph.edge u v = (tannerLevel P).graph.edge (vertexEquiv P u) (vertexEquiv P v) := rfl
end QEC.Coding.BDL26RXDecoderAdapter
