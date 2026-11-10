-- Prove2me | solution 1 for QEC.Coding.BDL26GraphQuantitativeBounds.parentNeighbors_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:47:04.859321+00:00
-- url     : https://prove2.me/submissions/3ac0abfa-9f22-4a46-b587-f5787be8b110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical
namespace QEC.Coding.BDL26GraphQuantitativeBounds
theorem _root_.solution (S : OddScale) (n : Nat)
    (v : GraphVertex S (n+1)) :
    Subsingleton {u : GraphVertex S n // v ∈ localRegion S n u} where
  allEq := by
    intro u w
    apply Subtype.ext
    exact Option.some.inj
      (((parent_mem_iff S n u.1 v).mpr u.2).symm.trans
        ((parent_mem_iff S n w.1 v).mpr w.2))
end QEC.Coding.BDL26GraphQuantitativeBounds
