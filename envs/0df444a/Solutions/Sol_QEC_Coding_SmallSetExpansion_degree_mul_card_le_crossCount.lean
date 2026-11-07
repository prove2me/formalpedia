-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.degree_mul_card_le_crossCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:59.177735+00:00
-- url     : https://prove2.me/submissions/bd5a2fa8-6765-4453-8a74-cdbeff8fdf1a

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (S T : Finset V) (degree : Nat)
    (hDegree : HasForwardDegreeAtLeast M S T degree) :
    degree * S.card ≤ crossCount M S T := by
  unfold crossCount
  calc
    degree * S.card = ∑ _v ∈ S, degree := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, ∑ u ∈ T, M v u := by
      exact Finset.sum_le_sum fun v hv => hDegree v hv
end QEC.Coding.SmallSetExpansion
