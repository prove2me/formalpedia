-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.map2_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:58:10.013997+00:00
-- url     : https://prove2.me/submissions/277ac478-9890-47ba-8791-75377ae14814

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (w : Word BDL26Field P.Z) (z : P.Z) (c : Fin 2) :
    rxMap2Coord P S w (zPairEquiv P S (z,c)).val = w z := rfl
end QEC.Coding.BDL26RXDecoderAdapter
