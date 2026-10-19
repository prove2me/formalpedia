-- Prove2me | solution 1 for TwoDegenerateGraphs.withoutReplacementBinaryPairExpectation_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/dd147f3d-9157-4bc0-9b92-3dcf8374c90c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairExpectation_sub

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by
  let q : ℝ := (oneCount : ℝ) / (parentCount : ℝ)
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hqzero : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hparent_real).mpr
    exact_mod_cast hones
  have hvariance : q * (1 - q) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hscaledvariance :=
    mul_le_mul_of_nonneg_right hvariance hparent_real.le
  have hdelta_nonneg : 0 ≤ q * (1 - q) / ((parentCount : ℝ) - 1) := by
    exact div_nonneg
      (mul_nonneg hqzero (sub_nonneg.mpr hqone))
      hparent_minus.le
  have hdelta_bound :
      2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) ≤
        1 / (parentCount : ℝ) := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    rw [show 2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) =
      (2 * (q * (1 - q))) / ((parentCount : ℝ) - 1) by ring]
    apply (div_le_div_iff₀ hparent_minus hparent_real).mpr
    nlinarith
  have hbracket :
      |f false true + f true false - f false false - f true true| ≤
        (2 : ℝ) := by
    rw [abs_le]
    have h₀₀ := hf false false
    have h₀₁ := hf false true
    have h₁₀ := hf true false
    have h₁₁ := hf true true
    constructor <;> linarith
  rw [withoutReplacementBinaryPairExpectation_sub
    parentCount oneCount hparents f, abs_mul]
  change
    |q * (1 - q) / ((parentCount : ℝ) - 1)| *
        |f false true + f true false - f false false - f true true| ≤
      1 / (parentCount : ℝ)
  rw [abs_of_nonneg hdelta_nonneg]
  calc
    (q * (1 - q) / ((parentCount : ℝ) - 1)) *
        |f false true + f true false - f false false - f true true| ≤
      (q * (1 - q) / ((parentCount : ℝ) - 1)) * 2 :=
        mul_le_mul_of_nonneg_left hbracket hdelta_nonneg
    _ ≤ 1 / (parentCount : ℝ) := by
      nlinarith
end TwoDegenerateGraphs
