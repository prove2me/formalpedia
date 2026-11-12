-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.actual_cartesian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:00:45.551215+00:00
-- url     : https://prove2.me/submissions/944709c6-bfab-41d3-86c4-1fd1b7dee659

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_product_cartesian

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
theorem _root_.solution (S : OddScale) (depth m : ℕ) (t : ℝ) :
    actualMass S depth m t=
      ∑ K ∈ BDL26ConnectedSetCounting.levelTwoSets S depth m,
        ∑ x : (∀ v : (show Finset (Node S depth) from K \ structural S depth),
          {w : Word Bit (OwnerFiber S v.val.1.val v.val.2) // w≠0}),
          Real.exp (-t*(∑ v : (show Finset (Node S depth) from K \ structural S depth),
            (HammingWeight (extend S v.val.1.val v.val.2 (x v).val) : ℝ))) := by
  unfold actualMass QEC.Locality.WeightedConnectedSetMass.occupiedMass
  apply Finset.sum_congr rfl
  intro K hK
  exact product_cartesian S depth (K \ structural S depth) t
end QEC.Coding.BDL26ConnectedSyndromeMass
