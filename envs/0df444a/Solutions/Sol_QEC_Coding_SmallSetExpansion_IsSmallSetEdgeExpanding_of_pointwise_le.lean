-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_pointwise_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:54.120939+00:00
-- url     : https://prove2.me/submissions/8332e123-330c-422b-b083-e32e004b9c61

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_mono

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    {M N : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hN : IsSmallSetEdgeExpanding N radius lambda)
    (hMN : ∀ v u, M v u ≤ N v u) :
    IsSmallSetEdgeExpanding M radius lambda := by
  intro S T hS hT
  calc
    (crossCount M S T : ℝ) ≤ crossCount N S T := by
      exact_mod_cast crossCount_mono hMN S T
    _ ≤ lambda * Real.sqrt ((S.card : ℝ) * T.card) := hN S T hS hT
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
