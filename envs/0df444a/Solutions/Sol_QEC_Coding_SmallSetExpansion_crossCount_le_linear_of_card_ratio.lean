-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.crossCount_le_linear_of_card_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:12.379017+00:00
-- url     : https://prove2.me/submissions/5a4ca748-7fd4-4a32-8366-545caecdb779

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V] [Nonempty V]
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (degree : Nat) (spectral fraction ratio uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction) (hRatio : 0 ≤ ratio)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (bad S T : Finset V)
    (hBad : (bad.card : ℝ) ≤ fraction * S.card)
    (hRatioBound : (S.card : ℝ) ≤ ratio * T.card)
    (hMean : (degree : ℝ) * bad.card ≤ uniformBudget * Fintype.card V) :
    (crossCount M bad T : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt (fraction * ratio)) * T.card := by
  have hn : (0 : ℝ) < Fintype.card V := by positivity
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hBadRatio : (bad.card : ℝ) ≤ fraction * ratio * T.card := by
    have hScaled := mul_le_mul_of_nonneg_left hRatioBound hFraction
    nlinarith
  have hRoot : Real.sqrt ((bad.card : ℝ) * T.card) ≤
      Real.sqrt (fraction * ratio) * T.card := by
    calc
      Real.sqrt ((bad.card : ℝ) * T.card) ≤
          Real.sqrt ((fraction * ratio) * (T.card : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = Real.sqrt (fraction * ratio) * T.card := by
        rw [Real.sqrt_mul (mul_nonneg hFraction hRatio), Real.sqrt_sq ht]
  have hMix := hMixing bad T
  have hMeanScaled := mul_le_mul_of_nonneg_right hMean ht
  have hRootScaled := mul_le_mul_of_nonneg_left hRoot (mul_nonneg hSpectral hn.le)
  have hScaled : (Fintype.card V : ℝ) * crossCount M bad T ≤
      (Fintype.card V : ℝ) *
        ((uniformBudget + spectral * Real.sqrt (fraction * ratio)) * T.card) := by
    nlinarith
  exact le_of_mul_le_mul_left hScaled hn
end QEC.Coding.SmallSetExpansion
