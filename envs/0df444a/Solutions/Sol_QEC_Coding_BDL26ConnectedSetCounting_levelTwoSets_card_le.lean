-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSetCounting.levelTwoSets_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:53:21.939657+00:00
-- url     : https://prove2.me/submissions/6873d493-5a28-4cf5-a14b-bb2ee8cbacf9

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_anchoredSets_card_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds
namespace QEC.Coding.BDL26ConnectedSetCounting
theorem _root_.solution (S : OddScale) (depth m : Nat) :
    (levelTwoSets S depth m).card ≤
      (levelTwoAnchors S depth).card * (14*S.ell^2+9)^(2*m) :=
  anchoredSets_card_le S depth _ m
end QEC.Coding.BDL26ConnectedSetCounting
