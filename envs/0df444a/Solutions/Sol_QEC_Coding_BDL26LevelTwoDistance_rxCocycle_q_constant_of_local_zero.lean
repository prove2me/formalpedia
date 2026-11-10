-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.rxCocycle_q_constant_of_local_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:27:52.767015+00:00
-- url     : https://prove2.me/submissions/55c2fdce-6586-4609-8448-90166737a4c7

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rxCoboundary1_qEdge_of_local_zero
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph
namespace QEC.Coding.BDL26LevelTwoDistance
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (word : Word Field (RX1 P S))
    (hc : rxCoboundary1 P S word = 0)
    (hx : ∀ x edge, word (Sum.inl ⟨x, edge⟩) = 0) (q : P.Q)
    (vertex : QDoubleCylinderVertex P q S) :
    word (Sum.inr ⟨q, vertex⟩) = word (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩) := by
  apply word_eq_root_of_graphCoboundary_eq_zero
    (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S)
    (0, Sum.inl (Sum.inl ())) (qDoubleCylinderPath P A q S)
    (fun v => word (Sum.inr ⟨q, v⟩)) ?_ vertex
  funext edge
  rw [wordLinearMapTranspose_graphBoundary_apply]
  rw [← rxCoboundary1_qEdge_of_local_zero P S word hx q edge, hc]
  rfl
end QEC.Coding.BDL26LevelTwoDistance
