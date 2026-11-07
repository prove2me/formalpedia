-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:57.552924+00:00
-- url     : https://prove2.me/submissions/e90b2af2-ed90-4ae4-afd8-0e072702544a

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    {M : WeightedGraph V} {radius radius' : Nat} {lambda lambda' : ℝ}
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hRadius : radius' ≤ radius) (hLambda : lambda ≤ lambda') :
    IsSmallSetEdgeExpanding M radius' lambda' := by
  intro S T hS hT
  calc
    (crossCount M S T : ℝ) ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card) :=
      hExpand S T (hS.trans hRadius) (hT.trans hRadius)
    _ ≤ lambda' * Real.sqrt ((S.card : ℝ) * T.card) :=
      mul_le_mul_of_nonneg_right hLambda (Real.sqrt_nonneg _)
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
