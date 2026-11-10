-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.anchors_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:10:16.210149+00:00
-- url     : https://prove2.me/submissions/03716bdb-ac0e-40a5-a5f3-30a1cda76934

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_mem_levelTwoAnchors


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
theorem _root_.solution (S : OddScale) (depth : ℕ) :
    Disjoint (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth) := by
  apply Finset.disjoint_left.mpr
  intro v ha hb
  have he := (BDL26ConnectedSetCounting.mem_levelTwoAnchors S depth v).mp ha
  have hl := (Finset.mem_filter.mp hb).2
  omega
end QEC.Coding.BDL26ConnectedSyndromeMass
