-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.relabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:48.123635+00:00
-- url     : https://prove2.me/submissions/3df31fd6-3263-442a-9548-3b6e291520be

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_relabel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    {U : Type*} [DecidableEq V] [DecidableEq U]
    {M : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda) (e : V ≃ U) :
    IsSmallSetEdgeExpanding (relabel e M) radius lambda := by
  intro S T hS hT
  rw [crossCount_relabel]
  simpa using hM (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding)
    (by simpa using hS) (by simpa using hT)
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
