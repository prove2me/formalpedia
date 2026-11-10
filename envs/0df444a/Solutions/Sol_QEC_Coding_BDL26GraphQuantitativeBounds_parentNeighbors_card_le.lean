-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:50:18.531285+00:00
-- url     : https://prove2.me/submissions/2662dc18-bd96-4434-a160-229d5b5420b5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_parentNeighbors_subsingleton

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat) (v : GraphVertex S (n+1)) :
    Fintype.card {u : GraphVertex S n // v ∈ localRegion S n u} ≤ 1 := by
  classical
  letI := parentNeighbors_subsingleton S n v
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
end QEC.Coding.BDL26GraphQuantitativeBounds
