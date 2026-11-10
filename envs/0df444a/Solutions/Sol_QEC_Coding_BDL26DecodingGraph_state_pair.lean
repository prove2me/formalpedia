-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.state_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:01:50.285193+00:00
-- url     : https://prove2.me/submissions/c6036cf3-6a52-45c6-817e-9b37abee6697

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
theorem _root_.solution (S : OddScale) (n : Nat) :
    Nonempty (Fin 2 ↪ Vertex (state S n).presentation) := by
  cases n with
  | zero =>
      refine ⟨⟨fun i => .x i, ?_⟩⟩
      intro i j h
      exact Vertex.x.inj h
  | succ n =>
      unfold state nextState
      split
      · let P := (state S n).presentation
        let x := (state S n).selectedX
        refine ⟨⟨fun i => .x (rxOriginalCentralXCoordinate P S x i), ?_⟩⟩
        intro i j h
        exact congrArg (fun c : (rxReplacementPresentation P S).X => c.2.1)
          (Vertex.x.inj h)
      · let C := state S n
        refine ⟨⟨fun i => .x (Sum.inr (C.selectedX, i)), ?_⟩⟩
        intro i j h
        exact congrArg Prod.snd (Sum.inr.inj (Vertex.x.inj h))
end QEC.Coding.BDL26DecodingGraph
