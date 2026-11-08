-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.IsSmallSetEdgeExpanding.square_of_symmetric_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:41.560394+00:00
-- url     : https://prove2.me/submissions/f834d696-ca2f-4ec5-83e9-a02c04b3cb97

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_square
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_incomingCount_eq_crossCount
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_outgoingCount_eq_crossCount
import Theorems.Thm_QEC_Coding_SmallSetExpansion_incomingCount_le_degree
import Theorems.Thm_QEC_Coding_SmallSetExpansion_card_intermediateSupport_le
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_mul_over_intermediateSupport
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_mul_le_of_dyadic_mixing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace IsSmallSetEdgeExpanding
theorem _root_.solution
    [Fintype V] [DecidableEq V]
    {M : WeightedGraph V} {radius degree : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda) :
    IsSmallSetEdgeExpanding (square M) (radius / degree)
      (((Nat.log 2 degree + 1 : Nat) : ℝ) * (2 * lambda ^ 2)) := by
  intro S T hS hT
  let p : V → Nat := incomingCount M S
  let q : V → Nat := outgoingCount M T
  let U : Finset V := intermediateSupport M S
  have hSRadius : S.card ≤ radius :=
    hS.trans (Nat.div_le_self radius degree)
  have hTRadius : T.card ≤ radius :=
    hT.trans (Nat.div_le_self radius degree)
  have hUCard : U.card ≤ radius := by
    calc
      U.card ≤ degree * S.card := card_intermediateSupport_le M degree hRegular S
      _ ≤ degree * (radius / degree) := Nat.mul_le_mul_left degree hS
      _ ≤ radius := Nat.mul_div_le radius degree
  have hPPos : ∀ x ∈ U, 0 < p x := by
    intro x hx
    have hxNe : incomingCount M S x ≠ 0 := (Finset.mem_filter.mp hx).2
    exact Nat.pos_of_ne_zero hxNe
  have hPBound : ∀ x ∈ U, p x ≤ degree := by
    intro x _hx
    exact incomingCount_le_degree M degree hSymm hRegular S x
  have hPMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (p x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * S.card) := by
    intro A hAU
    have hACard : A.card ≤ radius :=
      (Finset.card_le_card hAU).trans hUCard
    have hEq : (∑ x ∈ A, (p x : ℝ)) =
        (crossCount M A S : ℝ) := by
      exact_mod_cast sum_incomingCount_eq_crossCount M hSymm S A
    rw [hEq]
    exact hExpand A S hACard hSRadius
  have hQMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (q x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * T.card) := by
    intro A hAU
    have hACard : A.card ≤ radius :=
      (Finset.card_le_card hAU).trans hUCard
    have hEq : (∑ x ∈ A, (q x : ℝ)) =
        (crossCount M A T : ℝ) := by
      exact_mod_cast sum_outgoingCount_eq_crossCount M A T
    rw [hEq]
    exact hExpand A T hACard hTRadius
  have hDyadic := sum_mul_le_of_dyadic_mixing p q U degree lambda
    S.card T.card hLambda hPPos hPBound hPMix hQMix
  have hCross : (crossCount (square M) S T : ℝ) =
      ∑ x ∈ U, ((p x * q x : Nat) : ℝ) := by
    rw [crossCount_square, sum_mul_over_intermediateSupport, Nat.cast_sum]
  rw [hCross]
  calc
    (∑ x ∈ U, ((p x * q x : Nat) : ℝ)) ≤
        ((Nat.log 2 degree + 1 : Nat) : ℝ) *
          (2 * lambda ^ 2 * Real.sqrt ((S.card : ℝ) * T.card)) := hDyadic
    _ = (((Nat.log 2 degree + 1 : Nat) : ℝ) * (2 * lambda ^ 2)) *
        Real.sqrt ((S.card : ℝ) * T.card) := by ring
end IsSmallSetEdgeExpanding
end QEC.Coding.SmallSetExpansion
