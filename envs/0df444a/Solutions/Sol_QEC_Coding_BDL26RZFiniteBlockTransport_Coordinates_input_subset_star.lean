-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.input_subset_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:44:28.967193+00:00
-- url     : https://prove2.me/submissions/2605c945-9fc0-4544-9356-2ddb9b3f62ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)
namespace QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
theorem _root_.solution (Q0 : Finset P.Q) (Z0 : Finset P.Z) :
    inputBlocks P S Q0 Z0 ⊆ star P S Q0 Z0 := by
  intro p hp
  rcases p with ⟨z,e⟩ | ⟨q,v⟩
  · exact (mem_input_z P S _ _ _ _).mpr
      (Finset.mem_union_left _ ((mem_input_z P S _ _ _ _).mp hp))
  · exact (mem_input_q P S _ _ _ _).mpr ((mem_input_q P S _ _ _ _).mp hp)
end QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
