-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.sum_vertexIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:48.293868+00:00
-- url     : https://prove2.me/submissions/47f17dcb-6056-4593-8f38-6a3315a6d251

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, vertexIndicator S v = S.card := by
  classical
  change (∑ v ∈ Finset.univ, if v ∈ S then (1 : ℝ) else 0) = S.card
  rw [Finset.sum_boole]
  simp
end QEC.Coding.SmallSetExpansion
