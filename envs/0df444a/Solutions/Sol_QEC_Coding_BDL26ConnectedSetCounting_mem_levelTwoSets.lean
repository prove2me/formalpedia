-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSetCounting.mem_levelTwoSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:53:18.667885+00:00
-- url     : https://prove2.me/submissions/2f934d85-bace-4704-b118-75be3f70612d

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_anchored


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds
namespace QEC.Coding.BDL26ConnectedSetCounting
theorem _root_.solution (S : OddScale) (depth m : Nat)
    (A : Finset (decodingGraph S depth).Node) :
    A ∈ levelTwoSets S depth m ↔ A.card = m ∧
      ((graph S depth).induce (A : Set (decodingGraph S depth).Node)).Connected ∧
      (A ∩ levelTwoAnchors S depth).Nonempty :=
  Locality.ConnectedSetCounting.mem_anchored (graph S depth) _ m A
end QEC.Coding.BDL26ConnectedSetCounting
