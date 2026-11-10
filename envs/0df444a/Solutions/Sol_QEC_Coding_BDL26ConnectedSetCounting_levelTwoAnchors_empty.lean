-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSetCounting.levelTwoAnchors_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:10:23.241701+00:00
-- url     : https://prove2.me/submissions/08e427b5-3cfc-4188-b01d-3a222187e292

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Theorems.Thm_QEC_Coding_BDL26ConnectedSetCounting_mem_levelTwoAnchors

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSetCounting
open Classical MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26GraphQuantitativeBounds
namespace QEC.Coding.BDL26ConnectedSetCounting
theorem _root_.solution (S : OddScale) (depth : Nat) (hd : depth < 2) :
    levelTwoAnchors S depth = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have he := (mem_levelTwoAnchors S depth v).mp hv
  have hi := v.1.isLt
  omega
end QEC.Coding.BDL26ConnectedSetCounting
