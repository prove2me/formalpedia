-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:46.0192+00:00
-- url     : https://prove2.me/submissions/fed814bf-30d8-49df-86da-b96d2eb894d0

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {M N : WeightedGraph V} (hMN : ∀ v u, M v u ≤ N v u)
    (S T : Finset V) :
    crossCount M S T ≤ crossCount N S T := by
  unfold crossCount
  exact Finset.sum_le_sum fun v _hv =>
    Finset.sum_le_sum fun u _hu => hMN v u
end QEC.Coding.SmallSetExpansion
