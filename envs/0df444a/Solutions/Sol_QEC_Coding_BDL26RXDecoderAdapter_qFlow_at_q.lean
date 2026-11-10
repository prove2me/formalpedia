-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qFlow_at_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:24:35.530349+00:00
-- url     : https://prove2.me/submissions/eff18fbb-43ad-402e-b0e5-d3bf94050807

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_qzConnecting_at_q


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (q r : P.Q)
    (w : Word BDL26Field (QDoubleCylinderVertex P q S)) (e : QDoubleCylinderEdge P r S) :
    qFlow P S q w (Sum.inl (Sum.inr ⟨r,e⟩)) = 0 :=
  qzConnecting_at_q P S (qExtend P S q w) r e
end QEC.Coding.BDL26RXDecoderAdapter
