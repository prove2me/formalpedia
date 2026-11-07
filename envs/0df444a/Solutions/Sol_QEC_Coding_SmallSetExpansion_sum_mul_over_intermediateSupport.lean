-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_mul_over_intermediateSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:13.191007+00:00
-- url     : https://prove2.me/submissions/a19f084f-e975-4390-afea-8de367eea96e

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (S T : Finset V) :
    (∑ x, incomingCount M S x * outgoingCount M T x) =
      ∑ x ∈ intermediateSupport M S,
        incomingCount M S x * outgoingCount M T x := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _hxUniv hxSupport
  have hxZero : incomingCount M S x = 0 := by
    simpa [intermediateSupport] using hxSupport
  simp [hxZero]
end QEC.Coding.SmallSetExpansion
