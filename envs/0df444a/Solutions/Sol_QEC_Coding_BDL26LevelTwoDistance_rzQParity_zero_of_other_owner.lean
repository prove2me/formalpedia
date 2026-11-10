-- Prove2me | solution 1 for QEC.Coding.BDL26LevelTwoDistance.rzQParity_zero_of_other_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:37:05.979355+00:00
-- url     : https://prove2.me/submissions/f22e3a82-136a-4207-907d-93fed1323179

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
theorem _root_.solution (P : TannerSquarePresentation) (S : OddScale)
    (word : Word Field (RZQ P S)) (owner : Vertex P)
    (howner : ∀ coordinate, word coordinate ≠ 0 →
      BDL26ReplacementSupport.rzCorrectionOwner P S coordinate = owner)
    (q : P.Q) (hne : Vertex.q q ≠ owner) : rzQParity P S word q = 0 := by
  classical
  change (∑ vertex : QDoubleCylinderVertex (transposePresentation P) q S,
    word (Sum.inr ⟨q, vertex⟩)) = 0
  apply Finset.sum_eq_zero
  intro vertex _
  by_contra hn
  exact hne (howner (Sum.inr ⟨q, vertex⟩) hn)
end QEC.Coding.BDL26LevelTwoDistance
