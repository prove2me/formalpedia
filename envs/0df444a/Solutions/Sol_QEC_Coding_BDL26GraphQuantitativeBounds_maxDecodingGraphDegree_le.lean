-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.maxDecodingGraphDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:11:38.877976+00:00
-- url     : https://prove2.me/submissions/c2147dff-9bb0-4554-9756-420d4cc1a659

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_decodingGraph_degree_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
open BDL26ReplacementSupport
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (S : OddScale) (depth : Nat) :
    maxDecodingGraphDegree S depth ≤ fullGraphDegreeBound S := by
  classical
  apply Finset.sup_le
  intro u _
  exact decodingGraph_degree_bound S depth u
end QEC.Coding.BDL26GraphQuantitativeBounds
