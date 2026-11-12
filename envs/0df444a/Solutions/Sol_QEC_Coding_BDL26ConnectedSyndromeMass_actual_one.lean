-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.actual_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:59:56.332785+00:00
-- url     : https://prove2.me/submissions/b7c1890c-9b5e-4cf3-853b-cb094bf4afdd

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_anchors_disjoint
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_one


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
theorem _root_.solution (S : OddScale) (depth : ℕ) (t : ℝ) :
    actualMass S depth 1 t=∑ v ∈ BDL26ConnectedSetCounting.levelTwoAnchors S depth,
      factor S v.1.val v.2 t :=
  QEC.Locality.WeightedConnectedSetMass.occupied_one _ _ _ (anchors_disjoint S depth) _
end QEC.Coding.BDL26ConnectedSyndromeMass
