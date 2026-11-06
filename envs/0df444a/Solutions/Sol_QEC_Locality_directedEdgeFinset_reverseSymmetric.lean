-- Prove2me | solution 1 for QEC.Locality.directedEdgeFinset_reverseSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:11.0112+00:00
-- url     : https://prove2.me/submissions/7e31770f-42bc-4347-917b-90e5a7c711ea

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (G : ConnectivityGraph ι) :
    ReverseSymmetricEdgeSet (directedEdgeFinset G) := by
  intro x y
  rw [mem_directedEdgeFinset_iff, mem_directedEdgeFinset_iff]
  constructor
  · exact fun hxy => G.symmetric hxy
  · exact fun hyx => G.symmetric hyx
end QEC.Locality
