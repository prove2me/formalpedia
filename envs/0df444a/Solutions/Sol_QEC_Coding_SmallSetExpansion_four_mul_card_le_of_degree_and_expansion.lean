-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.four_mul_card_le_of_degree_and_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:59.884788+00:00
-- url     : https://prove2.me/submissions/e640267e-3ab2-405f-9961-4d74de713919

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_degree_mul_card_le_crossCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (radius degree : Nat) (lambda : ℝ)
    (hLambda : 0 < lambda)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (S L : Finset V) (hSRadius : S.card ≤ radius)
    (hLRadius : L.card ≤ radius)
    (hDegree : HasForwardDegreeAtLeast M S L degree)
    (hThreshold : 2 * lambda ≤ degree) :
    4 * S.card ≤ L.card := by
  by_cases hS : S.card = 0
  · simp [hS]
  have hSPosNat : 0 < S.card := Nat.pos_of_ne_zero hS
  have hSPos : (0 : ℝ) < S.card := by exact_mod_cast hSPosNat
  have hCountNat := degree_mul_card_le_crossCount M S L degree hDegree
  have hCount : (degree : ℝ) * S.card ≤ (crossCount M S L : ℝ) := by
    exact_mod_cast hCountNat
  have hMix := hExpand S L hSRadius hLRadius
  have hThreshold' : 2 * lambda ≤ (degree : ℝ) := by
    simpa using hThreshold
  have hLambdaScaled : lambda * (2 * (S.card : ℝ)) ≤
      lambda * Real.sqrt ((S.card : ℝ) * L.card) := by
    calc
      lambda * (2 * (S.card : ℝ)) =
          (2 * lambda) * (S.card : ℝ) := by ring
      _ ≤ (degree : ℝ) * S.card :=
        mul_le_mul_of_nonneg_right hThreshold' (le_of_lt hSPos)
      _ ≤ (crossCount M S L : ℝ) := hCount
      _ ≤ lambda * Real.sqrt ((S.card : ℝ) * L.card) := hMix
  have hRoot : 2 * (S.card : ℝ) ≤
      Real.sqrt ((S.card : ℝ) * L.card) := by
    nlinarith
  have hProductNonnegative :
      0 ≤ (S.card : ℝ) * L.card := mul_nonneg (by positivity) (by positivity)
  have hRootSq :
      (Real.sqrt ((S.card : ℝ) * L.card)) ^ 2 =
        (S.card : ℝ) * L.card := Real.sq_sqrt hProductNonnegative
  have hFourReal : 4 * (S.card : ℝ) ≤ L.card := by
    have hRootNonnegative := Real.sqrt_nonneg ((S.card : ℝ) * L.card)
    nlinarith
  exact_mod_cast hFourReal
end QEC.Coding.SmallSetExpansion
