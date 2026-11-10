-- Prove2me | solution 1 for QEC.Coding.BDL26IndexedDecoder.selectedMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:53:07.439232+00:00
-- url     : https://prove2.me/submissions/0ec2b43d-0cfa-4baa-ba60-71fbafd1e7a2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26ReplacementCochainMaps BDL26RZLocalReplacement BDL26RXLocalReplacement
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder BDL26AlternatingCochain
open scoped Classical
universe u
namespace QEC.Coding.BDL26IndexedDecoder
theorem _root_.solution (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    (indexedDecoderData S depth).selectedMap i = indexedEdgeMap S depth i := by
  unfold BDL26DecoderData.selectedMap
  split <;> rfl
end QEC.Coding.BDL26IndexedDecoder
