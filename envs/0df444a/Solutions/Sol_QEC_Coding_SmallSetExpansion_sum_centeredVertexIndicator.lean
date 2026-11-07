-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_centeredVertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:16.059037+00:00
-- url     : https://prove2.me/submissions/fd3d42d3-a497-41b0-b09d-48dd48264bb0

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_vertexIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, centeredVertexIndicator S v = 0 := by
  classical
  unfold centeredVertexIndicator
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator]
  simp
end QEC.Coding.SmallSetExpansion
