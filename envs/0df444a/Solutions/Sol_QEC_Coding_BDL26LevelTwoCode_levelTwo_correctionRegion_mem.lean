-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoCode.levelTwo_correctionRegion_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:59:04.450191+00:00
-- url     : https://prove2.me/submissions/93b05e4b-9ade-489f-a01f-640c59ce965c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Theorems.Thm_QEC_Coding_BDL26DecodingGraph_correctionRegion_mem
attribute [local simp] QEC.Coding.BDL26DecodingGraph.correctionRegion_mem



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators
namespace QEC.Coding.BDL26LevelTwoCode
theorem _root_.solution (S : OddScale)
    (u v : Vertex (levelTwoPresentation S)) :
    u ∈ (correctionRegion S 2 v).vertices ↔
      u = v ∨ tannerDirected (levelTwoPresentation S) u v = true :=
  correctionRegion_mem S 2 u v
end QEC.Coding.BDL26LevelTwoCode
