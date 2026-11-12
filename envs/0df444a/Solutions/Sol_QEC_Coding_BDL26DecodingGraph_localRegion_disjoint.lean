-- Prove2me | solution 1 for QEC.Coding.BDL26DecodingGraph.localRegion_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:54:28.922888+00:00
-- url     : https://prove2.me/submissions/4280c087-091f-4f22-b975-a341fa1bd3ef

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_DirectedDistance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26DecodingGraph
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
namespace QEC.Coding.BDL26DecodingGraph
theorem _root_.solution (S : OddScale) (n : Nat)
    (u w : GraphVertex S n) (hne : u ≠ w) :
    Disjoint (localRegion S n u) (localRegion S n w) := by
  apply Finset.disjoint_left.mpr
  intro v hu hw
  have hu' := (parent_mem_iff S n u v).mpr hu
  have hw' := (parent_mem_iff S n w v).mpr hw
  exact hne (Option.some.inj (hu'.symm.trans hw'))
end QEC.Coding.BDL26DecodingGraph
