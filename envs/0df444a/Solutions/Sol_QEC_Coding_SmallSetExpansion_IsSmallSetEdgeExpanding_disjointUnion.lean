-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:52.942865+00:00
-- url     : https://prove2.me/submissions/50c2d846-928d-4084-a82b-19c87dab6946

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_card_productFiber
import Theorems.Thm_QEC_Coding_SmallSetExpansion_card_productFiber_le
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_disjointUnion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {M : I → WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hM : ∀ i, IsSmallSetEdgeExpanding (M i) radius lambda) :
    IsSmallSetEdgeExpanding (disjointUnion M) radius lambda := by
  intro S T hS hT
  rw [crossCount_disjointUnion, Nat.cast_sum]
  have hFiberS (i : I) : (productFiber S i).card ≤ radius :=
    (card_productFiber_le S i).trans hS
  have hFiberT (i : I) : (productFiber T i).card ≤ radius :=
    (card_productFiber_le T i).trans hT
  calc
    ∑ i, (crossCount (M i) (productFiber S i) (productFiber T i) : ℝ) ≤
        ∑ i, lambda * Real.sqrt
          (((productFiber S i).card : ℝ) * (productFiber T i).card) :=
      Finset.sum_le_sum fun i _hi => hM i _ _ (hFiberS i) (hFiberT i)
    _ = lambda * ∑ i, Real.sqrt ((productFiber S i).card : ℝ) *
          Real.sqrt ((productFiber T i).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ lambda * (Real.sqrt (∑ i, ((productFiber S i).card : ℝ)) *
          Real.sqrt (∑ i, ((productFiber T i).card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)) hLambda
    _ = lambda * Real.sqrt ((S.card : ℝ) * T.card) := by
      have hSumS : ∑ i, ((productFiber S i).card : ℝ) = S.card := by
        exact_mod_cast sum_card_productFiber S
      have hSumT : ∑ i, ((productFiber T i).card : ℝ) = T.card := by
        exact_mod_cast sum_card_productFiber T
      rw [hSumS, hSumT, Real.sqrt_mul (Nat.cast_nonneg S.card)]
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
