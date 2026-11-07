-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_incomingCount_eq_crossCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:37.220823+00:00
-- url     : https://prove2.me/submissions/8096dc17-e08a-40e8-adb5-8a23ee482d06

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S A : Finset V) :
    (∑ x ∈ A, incomingCount M S x) = crossCount M A S := by
  simp only [incomingCount, crossCount]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro v _hv
  exact hSymm v x
end QEC.Coding.SmallSetExpansion
