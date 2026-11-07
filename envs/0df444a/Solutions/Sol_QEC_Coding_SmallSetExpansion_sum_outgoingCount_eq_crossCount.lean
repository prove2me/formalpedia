-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_outgoingCount_eq_crossCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:52.659706+00:00
-- url     : https://prove2.me/submissions/c6c72d4e-da8c-4fee-b826-24d8dc0eede6

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (A T : Finset V) :
    (∑ x ∈ A, outgoingCount M T x) = crossCount M A T := by
  rfl
end QEC.Coding.SmallSetExpansion
