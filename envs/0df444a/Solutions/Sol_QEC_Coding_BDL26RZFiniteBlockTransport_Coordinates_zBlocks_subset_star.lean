-- Prove2me | solution 1 for QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.zBlocks_subset_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:13:47.610682+00:00
-- url     : https://prove2.me/submissions/0a12d170-ecfd-41d3-a274-2fff61ad459c

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
    zBlocks P S (zplus P Q0 Z0) ⊆ star P S Q0 Z0 := Finset.subset_union_right
end QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
