-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:01.522937+00:00
-- url     : https://prove2.me/submissions/3076dfb4-03bc-461f-b5fe-9a94a56ab0f6

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_centeredVertexIndicator
import Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_sq_centeredVertexIndicator
import Theorems.Thm_QEC_Coding_SmallSetExpansion_adjacencyPairing_centeredVertexIndicator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace HasMeanZeroBilinearBound
theorem _root_.solution
    [Fintype V] [DecidableEq V] [Nonempty V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : HasMeanZeroBilinearBound M spectral) :
    HasExpanderMixingBound M degree spectral := by
  intro S T
  let n : ℝ := Fintype.card V
  let s : ℝ := S.card
  let t : ℝ := T.card
  let x : ℝ := Real.sqrt (s * t)
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hsn : s ≤ n := by
    dsimp [s, n]
    exact_mod_cast Finset.card_le_univ S
  have htn : t ≤ n := by
    dsimp [t, n]
    exact_mod_cast Finset.card_le_univ T
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = s * t := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hComplement : (n - s) * (n - t) ≤ n * n := by
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hNormS :
      (∑ v, (centeredVertexIndicator S v) ^ 2) = n * s * (n - s) := by
    simpa [n, s] using sum_sq_centeredVertexIndicator S
  have hNormT :
      (∑ v, (centeredVertexIndicator T v) ^ 2) = n * t * (n - t) := by
    simpa [n, t] using sum_sq_centeredVertexIndicator T
  have hSqrtNorm :
      Real.sqrt
          ((∑ v, (centeredVertexIndicator S v) ^ 2) *
            ∑ v, (centeredVertexIndicator T v) ^ 2) ≤
        n ^ 2 * x := by
    rw [hNormS, hNormT]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        (n * s * (n - s)) * (n * t * (n - t)) =
            (n ^ 2 * (s * t)) * ((n - s) * (n - t)) := by ring
        _ ≤ (n ^ 2 * (s * t)) * (n * n) :=
          mul_le_mul_of_nonneg_left hComplement (by positivity)
        _ = (n ^ 2 * x) ^ 2 := by rw [← hx2]; ring
  have hBound := hSpectral
    (centeredVertexIndicator S) (centeredVertexIndicator T)
    (sum_centeredVertexIndicator S) (sum_centeredVertexIndicator T)
  rw [adjacencyPairing_centeredVertexIndicator
    M degree hSymm hRegular S T] at hBound
  have hPairUpper :
      n * (n * (crossCount M S T : ℝ) -
          degree * s * t) ≤
        spectral *
          Real.sqrt
            ((∑ v, (centeredVertexIndicator S v) ^ 2) *
              ∑ v, (centeredVertexIndicator T v) ^ 2) := by
    exact (le_abs_self _).trans (by simpa [n, s, t] using hBound)
  have hSharp :
      n * (n * (crossCount M S T : ℝ) - degree * s * t) ≤
        spectral * (n ^ 2 * x) :=
    hPairUpper.trans
      (mul_le_mul_of_nonneg_left hSqrtNorm hSpectralNonnegative)
  change n * (crossCount M S T : ℝ) ≤
    (degree : ℝ) * s * t + spectral * n * x
  nlinarith
end HasMeanZeroBilinearBound
end QEC.Coding.SmallSetExpansion
