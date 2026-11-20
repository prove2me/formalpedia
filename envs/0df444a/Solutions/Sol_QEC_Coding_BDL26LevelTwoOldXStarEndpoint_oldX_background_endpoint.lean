-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_background_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:39:56.930709+00:00
-- url     : https://prove2.me/submissions/904f9c9f-2f15-42de-ba9b-79a106996bea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_two_search_endpoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoOldXStarEndpoint
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder BDL26DecodingGraph
open scoped Classical BigOperators
attribute [local instance] QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldXActualQFintype
namespace QEC.Coding.BDL26LevelTwoOldXStarEndpoint
theorem _root_.solution (S : OddScale) (x : (P S).X)
    (c : BDL26FiniteTannerSquare.Two) (a h : Word F (C S).Q)
    (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hs : firstSearch S (tannerCoboundary1 (C S) a)=some ws)
    (ht : firstSearch S (tannerCoboundary1 (C S) (a+h))=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=
      h+decode S (tannerCoboundary1 (C S) a)+decode S (tannerCoboundary1 (C S) (a+h)) := by
  apply oldX_two_search_endpoint S x c h _ _ ws wt hh _ hs ht
  rw [map_add,← add_assoc,ZModModule.add_self,zero_add]
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
