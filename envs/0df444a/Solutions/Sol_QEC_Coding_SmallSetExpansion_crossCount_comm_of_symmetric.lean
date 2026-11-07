-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_comm_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:21.279657+00:00
-- url     : https://prove2.me/submissions/5a7cf98b-69e6-41c0-9d2f-034f76fccf06

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [DecidableEq V]
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S T : Finset V) :
    crossCount M S T = crossCount M T S := by
  unfold crossCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v _hv
  exact hSymm v u
end QEC.Coding.SmallSetExpansion
