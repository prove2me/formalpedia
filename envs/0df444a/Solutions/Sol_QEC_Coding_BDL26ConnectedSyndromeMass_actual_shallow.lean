-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.actual_shallow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:58:59.997273+00:00
-- url     : https://prove2.me/submissions/3cd65cd1-a17e-4b6c-b0d8-53360cd3a3ca

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_levelTwoAnchors_empty
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_empty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (depth m : ℕ) (hd : depth<2) (t : ℝ) :
    actualMass S depth m t=0 := by
  unfold actualMass
  rw [BDL26ConnectedSetCounting.levelTwoAnchors_empty S depth hd]
  exact QEC.Locality.WeightedConnectedSetMass.occupied_empty _ _ _ _
end QEC.Coding.BDL26ConnectedSyndromeMass
