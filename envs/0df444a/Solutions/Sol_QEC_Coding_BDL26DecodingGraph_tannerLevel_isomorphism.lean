-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.tannerLevel_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:53:52.73462+00:00
-- url     : https://prove2.me/submissions/bb050422-18f0-4f97-99e2-b3e08b101cd1

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
    LevelGraphTannerIsomorphism (tannerLevel P) (tannerSkeleton P)
      (vertexKind P) (Equiv.refl (Vertex P)) :=
  ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩
end QEC.Coding.BDL26DecodingGraph
