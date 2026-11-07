-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.highDegree_card_bound_of_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:06.820812+00:00
-- url     : https://prove2.me/submissions/cfad4117-69d4-4e53-b31d-e762d8107acf

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V] [Nonempty V]
namespace QEC.Coding.SmallSetExpansion
theorem _root_.solution
    (M : WeightedGraph V) (degree : Nat) (spectral threshold : ℝ)
    (hSpectral : 0 ≤ spectral) (hThreshold : 0 < threshold)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (S T : Finset V)
    (hDegree : threshold * S.card ≤ (crossCount M S T : ℝ))
    (hDensity : 2 * (degree : ℝ) * T.card ≤ threshold * Fintype.card V) :
    threshold ^ 2 * S.card ≤ 4 * spectral ^ 2 * T.card := by
  by_cases hS : S.card = 0
  · simp [hS]
    positivity
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hn : (0 : ℝ) < Fintype.card V := by positivity
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hroot : 0 ≤ Real.sqrt ((S.card : ℝ) * T.card) := Real.sqrt_nonneg _
  have hDensityScaled := mul_le_mul_of_nonneg_right hDensity hs.le
  have hDegreeScaled := mul_le_mul_of_nonneg_left hDegree hn.le
  have hMix := hMixing S T
  have hScaledN : (Fintype.card V : ℝ) * (threshold / 2 * S.card) ≤
      (Fintype.card V : ℝ) * (spectral * Real.sqrt ((S.card : ℝ) * T.card)) := by
    nlinarith
  have hScaled : threshold / 2 * S.card ≤
      spectral * Real.sqrt ((S.card : ℝ) * T.card) :=
    le_of_mul_le_mul_left hScaledN hn
  have hSquare : (threshold / 2 * S.card) ^ 2 ≤
      (spectral * Real.sqrt ((S.card : ℝ) * T.card)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hScaled
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hs.le ht)] at hSquare
  have hCancel : (S.card : ℝ) * (threshold ^ 2 * S.card) ≤
      (S.card : ℝ) * (4 * spectral ^ 2 * T.card) := by
    nlinarith
  exact le_of_mul_le_mul_left hCancel hs
end QEC.Coding.SmallSetExpansion
