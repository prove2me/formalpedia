-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_relabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:16.810067+00:00
-- url     : https://prove2.me/submissions/800cd41c-9d8a-479b-a1c4-c763e4ed2aea

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    {U : Type*} [DecidableEq V] [DecidableEq U]
    (e : V ≃ U) (M : WeightedGraph V) (S T : Finset U) :
    crossCount (relabel e M) S T =
      crossCount M (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding) := by
  classical
  simp [crossCount, relabel]
end QEC.Coding.SmallSetExpansion
