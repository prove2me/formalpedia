-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.logMin_of_widthBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:43.957999+00:00
-- url     : https://prove2.me/submissions/a74dda5d-441c-4bb9-a7d5-32a1662e53f5

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rOut_sub_rIn_le_two_width

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hwidthLog :
      ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
          (128 * (2 ^ (2 * annulusWidth A K n) : ℝ))) :
    ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
        (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)) := by
  have hpow_le : (2 ^ (rOut A K n - rIn A K n) : ℝ) ≤
      (2 ^ (2 * annulusWidth A K n) : ℝ) := by
    exact_mod_cast
      Nat.pow_le_pow_right (by decide : 0 < 2)
        (rOut_sub_rIn_le_two_width (A := A) (K := K) (n := n))
  have hden_le : 128 * (2 ^ (rOut A K n - rIn A K n) : ℝ) ≤
      128 * (2 ^ (2 * annulusWidth A K n) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hpow_le (by norm_num)
  have hden_pos : 0 < 128 * (2 ^ (rOut A K n - rIn A K n) : ℝ) := by
    positivity
  have hnum_nonneg : 0 ≤ (loss n) ^ 2 * (minPile (splitM K n) : ℝ) := by
    positivity
  have hfrac :
      (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
          (128 * (2 ^ (2 * annulusWidth A K n) : ℝ)) ≤
        (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
          (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)) :=
    div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  exact hwidthLog.trans hfrac
end PebblingLean.Hypercube.PaperParameters
