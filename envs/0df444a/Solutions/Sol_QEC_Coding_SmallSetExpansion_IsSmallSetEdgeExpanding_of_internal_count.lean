-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.of_internal_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:36.205983+00:00
-- url     : https://prove2.me/submissions/4475e41c-77c0-4b02-bbb5-a9dc694f5a89

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_mono_sets
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_comm_of_symmetric
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_le_degree_mul_card_left

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (radius degree : Nat) (internalConstant : ℝ)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset V, U.card ≤ 2 * radius →
      (crossCount M U U : ℝ) ≤ internalConstant * U.card) :
    IsSmallSetEdgeExpanding M radius
      (Real.sqrt (2 * internalConstant * degree)) := by
  intro S T hS hT
  have hFactorNonnegative : 0 ≤ 2 * internalConstant * (degree : ℝ) := by
    positivity
  have bound_when_card_le
      (A B : Finset V) (hA : A.card ≤ radius) (hB : B.card ≤ radius)
      (hAB : A.card ≤ B.card) :
      (crossCount M A B : ℝ) ≤
        Real.sqrt (2 * internalConstant * degree) *
          Real.sqrt ((A.card : ℝ) * B.card) := by
    have hDegreeNat := crossCount_le_degree_mul_card_left
      M degree hRegular A B
    have hDegree : (crossCount M A B : ℝ) ≤
        (degree : ℝ) * A.card := by
      exact_mod_cast hDegreeNat
    have hUnionAB : (A ∪ B).card ≤ 2 * radius := by
      calc
        (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
        _ ≤ radius + radius := Nat.add_le_add hA hB
        _ = 2 * radius := by omega
    have hABUnionNat :
        crossCount M A B ≤ crossCount M (A ∪ B) (A ∪ B) :=
      crossCount_mono_sets M Finset.subset_union_left Finset.subset_union_right
    have hABUnion : (crossCount M A B : ℝ) ≤
        internalConstant * (A ∪ B).card :=
      (Nat.cast_le.mpr hABUnionNat).trans (hInternal (A ∪ B) hUnionAB)
    have hUnionLe : ((A ∪ B).card : ℝ) ≤ 2 * B.card := by
      exact_mod_cast (Finset.card_union_le A B).trans (by omega)
    have hInternalB : (crossCount M A B : ℝ) ≤
        2 * internalConstant * B.card := by
      calc
        (crossCount M A B : ℝ) ≤
            internalConstant * (A ∪ B).card := hABUnion
        _ ≤ internalConstant * (2 * B.card) :=
          mul_le_mul_of_nonneg_left hUnionLe hInternalNonnegative
        _ = 2 * internalConstant * B.card := by ring
    have hSquare : (crossCount M A B : ℝ) ^ 2 ≤
        (2 * internalConstant * degree) *
          ((A.card : ℝ) * B.card) := by
      calc
        (crossCount M A B : ℝ) ^ 2 =
            (crossCount M A B : ℝ) * crossCount M A B := by ring
        _ ≤ ((degree : ℝ) * A.card) *
            (2 * internalConstant * B.card) :=
          mul_le_mul hDegree hInternalB (Nat.cast_nonneg _) (by positivity)
        _ = (2 * internalConstant * degree) *
            ((A.card : ℝ) * B.card) := by ring
    have hSqrt : (crossCount M A B : ℝ) ≤
        Real.sqrt ((2 * internalConstant * degree) *
          ((A.card : ℝ) * B.card)) :=
      Real.le_sqrt_of_sq_le hSquare
    rw [Real.sqrt_mul hFactorNonnegative] at hSqrt
    exact hSqrt
  by_cases hST : S.card ≤ T.card
  · exact bound_when_card_le S T hS hT hST
  · rw [crossCount_comm_of_symmetric M hSymm S T]
    have hTS : T.card ≤ S.card := Nat.le_of_not_ge hST
    simpa [mul_comm] using bound_when_card_le T S hT hS hTS
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
