-- Prove2me | solution 1 for QEC.Locality.separatorRightEdges_subset_directed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:23.690801+00:00
-- url     : https://prove2.me/submissions/8f3470b3-2053-460e-bf1a-9b11931ee6fe

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (left : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G) :
    separatorRightEdges edges left ⊆ directedEdgeFinset G :=
  (Finset.filter_subset _ _).trans hsubset
end QEC.Locality
