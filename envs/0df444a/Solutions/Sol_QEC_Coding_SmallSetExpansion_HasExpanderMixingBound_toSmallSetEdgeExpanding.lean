-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.HasExpanderMixingBound.toSmallSetEdgeExpanding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:06.839177+00:00
-- url     : https://prove2.me/submissions/b061e041-ba11-47ae-a028-48e265b71c1c

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace HasExpanderMixingBound
theorem _root_.solution
    [Fintype V] [Nonempty V]
    {M : WeightedGraph V} {degree radius : Nat} {spectral density : ℝ}
    (hMixing : HasExpanderMixingBound M degree spectral)
    (hDensity : (degree : ℝ) * radius ≤ density * Fintype.card V) :
    IsSmallSetEdgeExpanding M radius (spectral + density) := by
  intro S T hS hT
  let n : ℝ := Fintype.card V
  let s : ℝ := S.card
  let t : ℝ := T.card
  let x : ℝ := Real.sqrt (s * t)
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hs : s ≤ radius := by
    dsimp [s]
    exact_mod_cast hS
  have ht : t ≤ radius := by
    dsimp [t]
    exact_mod_cast hT
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = s * t := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hxRadius : x ≤ radius := by nlinarith
  have hProduct : s * t ≤ (radius : ℝ) * x := by nlinarith
  have hUniform : (degree : ℝ) * s * t ≤ density * n * x := by
    calc
      (degree : ℝ) * s * t ≤ (degree : ℝ) * ((radius : ℝ) * x) := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hProduct (Nat.cast_nonneg degree))
      _ = ((degree : ℝ) * radius) * x := by ring
      _ ≤ (density * n) * x := by
        exact mul_le_mul_of_nonneg_right (by simpa [n] using hDensity) hx0
      _ = density * n * x := by ring
  have hMix := hMixing S T
  change n * (crossCount M S T : ℝ) ≤
    (degree : ℝ) * s * t + spectral * n * x at hMix
  change (crossCount M S T : ℝ) ≤ (spectral + density) * x
  nlinarith
end HasExpanderMixingBound
end QEC.Coding.SmallSetExpansion
