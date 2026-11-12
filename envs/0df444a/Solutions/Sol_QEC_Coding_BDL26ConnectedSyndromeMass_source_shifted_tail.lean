-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.source_shifted_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:01:48.858749+00:00
-- url     : https://prove2.me/submissions/b4443d1b-6fdd-4c4d-98e6-8729d130080a

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_shifted_tail

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
theorem _root_.solution (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (beta : ℝ) (hq : ratio S (beta/4)<1) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m (beta/4)) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S (beta/4)^(L-10)/(1-ratio S (beta/4)) :=
  actual_shifted_tail S depth L U hd (beta/4) hq hL
end QEC.Coding.BDL26ConnectedSyndromeMass
