-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoOldXStarEndpoint.oldX_two_search_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:35.137173+00:00
-- url     : https://prove2.me/submissions/eecc4fbf-e770-4ff2-b9ec-fb7b8fbd00aa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoOldXStarEndpoint
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_firstSearch_sound
import Theorems.Thm_QEC_Coding_BDL26LevelTwoOldXStarEndpoint_oldX_two_local_full_potential

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
    (c : BDL26FiniteTannerSquare.Two) (h : Word F (C S).Q)
    (s t : Word F (C S).Z) (ws wt : Word F (ExecutableQ S))
    (hh : hammingSupport h ⊆ BDL26RXPhysicalStarTransport.physicalXStar (C S) (Sum.inr (x,c)))
    (hsyn : tannerCoboundary1 (C S) h=s+t)
    (hs : firstSearch S s=some ws) (ht : firstSearch S t=some wt) :
    ∃ p : Word F (C S).X, tannerCoboundary0 (C S) p=h+decode S s+decode S t := by
  have hds := firstSearch_sound S s ws hs
  have hdt := firstSearch_sound S t wt ht
  have hc : tannerCoboundary1 (C S) (h+decode S s+decode S t)=0 := by
    rw [map_add,map_add,hsyn,hds.2.2,hdt.2.2]
    calc
      s+t+s+t=(s+s)+(t+t) := by abel
      _=0 := by rw [ZModModule.add_self,ZModModule.add_self,add_zero]
  obtain ⟨g,edges,faces,hp⟩ := oldX_two_local_full_potential S x c h _ _ hh hds.2.1 hdt.2.1 hc
  exact ⟨_,hp⟩
end QEC.Coding.BDL26LevelTwoOldXStarEndpoint
