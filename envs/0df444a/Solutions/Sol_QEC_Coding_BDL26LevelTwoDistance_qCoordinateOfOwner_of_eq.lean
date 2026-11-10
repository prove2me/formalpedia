-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.qCoordinateOfOwner_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:37:15.73451+00:00
-- url     : https://prove2.me/submissions/d7186a11-1703-4d60-8460-42f6d0109196

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation) (defaultQ q : P.Q)
    (owner : Vertex P) (h : Vertex.q q = owner) :
    q = qCoordinateOfOwner P defaultQ owner := by
  subst owner
  rfl
end QEC.Coding.BDL26LevelTwoDistance
