-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.state_tannerDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:50:28.680694+00:00
-- url     : https://prove2.me/submissions/090b0495-6db6-4ca5-a9e7-138967cd54d8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_tannerDegree_le
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat)
    (v : Vertex (state S n).presentation) : tannerDegree (state S n).presentation v ≤ 7 :=
  tannerDegree_le _ (state_boundedValence S n) v
end QEC.Coding.BDL26GraphQuantitativeBounds
