-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.xExtend_at_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:17:16.940488+00:00
-- url     : https://prove2.me/submissions/3b9f309c-30bc-44ff-988b-833835707f78

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (w : Word BDL26Field (DoubleCylinderEdge P x S)) (q : P.Q)
    (v : QDoubleCylinderVertex P q S) : xExtend P S x w (Sum.inr ⟨q,v⟩) = 0 := by
  change extendLocalSignal ((localX P S).correctionRegion x) _ (Sum.inr ⟨q,v⟩) = 0
  rw [extendLocalSignal, dif_neg]
  intro hp
  have h := (Finset.mem_filter.mp hp).2
  cases h
end QEC.Coding.BDL26RXDecoderAdapter
