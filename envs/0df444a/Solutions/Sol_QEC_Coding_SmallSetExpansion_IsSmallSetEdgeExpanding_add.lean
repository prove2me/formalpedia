-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:46.982195+00:00
-- url     : https://prove2.me/submissions/ab5ce2e5-3b03-4ca2-a170-a41163a2c1e6

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    {M N : WeightedGraph V} {radius : Nat} {lambda mu : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda)
    (hN : IsSmallSetEdgeExpanding N radius mu) :
    IsSmallSetEdgeExpanding (add M N) radius (lambda + mu) := by
  intro S T hS hT
  rw [crossCount_add, Nat.cast_add]
  calc
    (crossCount M S T : ℝ) + crossCount N S T ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card) +
          mu * Real.sqrt ((S.card : ℝ) * T.card) :=
      add_le_add (hM S T hS hT) (hN S T hS hT)
    _ = (lambda + mu) * Real.sqrt ((S.card : ℝ) * T.card) := by ring
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
