-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:10.041509+00:00
-- url     : https://prove2.me/submissions/a3536f91-4be7-4a5b-8bde-7a0e4fa299bf

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution (M N : WeightedGraph V) (S T : Finset V) :
    crossCount (add M N) S T = crossCount M S T + crossCount N S T := by
  simp [crossCount, add, Finset.sum_add_distrib]
end QEC.Coding.SmallSetExpansion
