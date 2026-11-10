-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.tannerDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:47:02.091348+00:00
-- url     : https://prove2.me/submissions/da84c859-88f9-47a6-b0de-37816b87aa82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (P : TannerSquarePresentation) (h : BoundedValence P)
    (v : Vertex P) : tannerDegree P v ≤ 7 := by
  unfold tannerDegree
  cases v with
  | x x => rw [Fintype.card_congr (xNeighborEquiv P x)]; exact h.1 x
  | z z => rw [Fintype.card_congr (zNeighborEquiv P z)]; exact h.2.1 z
  | q q =>
      rw [Fintype.card_congr (qNeighborEquiv P q),Fintype.card_sum]
      exact (h.2.2 q).2.2
end QEC.Coding.BDL26GraphQuantitativeBounds
