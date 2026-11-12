-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.actual_prefix_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:01:32.276337+00:00
-- url     : https://prove2.me/submissions/257ec40f-d0b4-4120-ad7b-8b4eb073bb60

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_envelope_nonneg
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_factor_bounds
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_anchors_disjoint
import Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_graph_degree_bound
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_occupied_interval_strong


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
theorem _root_.solution (S : OddScale) (depth L U : ℕ) (t : ℝ) (hq : ratio S t<1) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        QEC.Locality.WeightedConnectedSetMass.structuralEnvelope (alphabet S) (envelope S t) (structural S depth).card L U :=
  QEC.Locality.WeightedConnectedSetMass.occupied_interval_strong _ _ (BDL26ConnectedSetCounting.graph_degree_bound S depth)
    _ _ (anchors_disjoint S depth) _ _ (envelope_nonneg S t)
    (fun v => (factor_bounds S v.1.val v.2 t).1)
    (fun v => (factor_bounds S v.1.val v.2 t).2) hq L U
end QEC.Coding.BDL26ConnectedSyndromeMass
