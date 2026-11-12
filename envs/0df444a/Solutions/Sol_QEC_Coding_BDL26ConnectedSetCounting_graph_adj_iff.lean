-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSetCounting.graph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:52:49.995693+00:00
-- url     : https://prove2.me/submissions/60a94e7e-dd54-4ae7-90e8-191576c6008c

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds
namespace QEC.Coding.BDL26ConnectedSetCounting
theorem _root_.solution (S : OddScale) (depth : Nat) (u v : (decodingGraph S depth).Node) :
    (graph S depth).Adj u v ↔ (decodingGraph S depth).adjacent u v := Iff.rfl
end QEC.Coding.BDL26ConnectedSetCounting
