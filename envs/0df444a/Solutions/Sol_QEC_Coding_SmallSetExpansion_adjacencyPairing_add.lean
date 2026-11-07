-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.adjacencyPairing_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:18.06221+00:00
-- url     : https://prove2.me/submissions/15608824-e2b9-455f-9b83-15dd099dbf99

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution (M N : WeightedGraph V) (f g : V → ℝ) :
    adjacencyPairing (add M N) f g = adjacencyPairing M f g + adjacencyPairing N f g := by
  classical
  simp only [adjacencyPairing, add, Nat.cast_add, add_mul, Finset.sum_add_distrib, mul_add]
end QEC.Coding.SmallSetExpansion
