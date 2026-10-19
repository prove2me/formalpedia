-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.conditionalEntropy_logsum_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/3bb48c21-6c19-4c69-97fe-7cf4813479f5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binary_log_sum_bound
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_eq_four_outcomes
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_conditionalEntropy_mul_log_two
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_averageDisagreement_eq_four_outcomes

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy * Real.log 2 -
        Real.binEntropy kernel.childMarginal / 2 -
        Real.log 3 * kernel.averageDisagreement ≤
      binaryConditionalLogPotential kernel.parentProbability
          (Real.sqrt (1 - kernel.childMarginal))
          (Real.sqrt kernel.childMarginal) -
        Real.binEntropy kernel.parentProbability / 2 := by
  let q : ℝ := kernel.parentProbability
  let v : ℝ := kernel.childMarginal
  let a : ℝ := Real.sqrt (1 - v)
  let b : ℝ := Real.sqrt v
  let z₀₀ : ℝ := kernel.childProbability false false
  let z₀₁ : ℝ := kernel.childProbability false true
  let z₁₀ : ℝ := kernel.childProbability true false
  let z₁₁ : ℝ := kernel.childProbability true true
  have hqzero : 0 ≤ q := kernel.parentProbability_nonneg
  have hqone : q ≤ 1 := kernel.parentProbability_le_one
  have hvzero : 0 < v := hmarginal_zero
  have hvone : v < 1 := hmarginal_one
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hvone)
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.mpr hvzero
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have h₀₀ := binary_log_sum_bound z₀₀ a (b / 3)
    (kernel.childProbability_nonneg false false)
    (kernel.childProbability_le_one false false)
    ha (by positivity)
  have h₀₁ := binary_log_sum_bound z₀₁
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg false true)
    (kernel.childProbability_le_one false true)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₀ := binary_log_sum_bound z₁₀
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg true false)
    (kernel.childProbability_le_one true false)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₁ := binary_log_sum_bound z₁₁ (a / 3) b
    (kernel.childProbability_nonneg true true)
    (kernel.childProbability_le_one true true)
    (by positivity) hb
  have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hscaled₀₀ := mul_le_mul_of_nonneg_left h₀₀
    (sq_nonneg (1 - q))
  have hscaled₀₁ := mul_le_mul_of_nonneg_left h₀₁
    (mul_nonneg hcomplement hqzero)
  have hscaled₁₀ := mul_le_mul_of_nonneg_left h₁₀
    (mul_nonneg hqzero hcomplement)
  have hscaled₁₁ := mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg q)
  have hcombined := add_le_add
    (add_le_add (add_le_add hscaled₀₀ hscaled₀₁) hscaled₁₀)
    hscaled₁₁
  have hmarginal :
      v =
        (1 - q) ^ 2 * z₀₀ +
          (1 - q) * q * z₀₁ +
          q * (1 - q) * z₁₀ +
          q ^ 2 * z₁₁ := by
    simpa [q, v, z₀₀, z₀₁, z₁₀, z₁₁] using
      childMarginal_eq_four_outcomes kernel
  have hentropy :
      kernel.conditionalEntropy * Real.log 2 =
        (1 - q) ^ 2 * Real.binEntropy z₀₀ +
          (1 - q) * q * Real.binEntropy z₀₁ +
          q * (1 - q) * Real.binEntropy z₁₀ +
          q ^ 2 * Real.binEntropy z₁₁ := by
    simpa [q, z₀₀, z₀₁, z₁₀, z₁₁] using
      conditionalEntropy_mul_log_two kernel
  have hdisagreement :
      kernel.averageDisagreement =
        (1 - q) ^ 2 * z₀₀ +
          q * (1 - q) + q ^ 2 * (1 - z₁₁) := by
    simpa [q, z₀₀, z₁₁] using
      averageDisagreement_eq_four_outcomes kernel
  have hloga : Real.log a = Real.log (1 - v) / 2 := by
    dsimp [a]
    exact Real.log_sqrt (sub_pos.mpr hvone).le
  have hlogb : Real.log b = Real.log v / 2 := by
    dsimp [b]
    exact Real.log_sqrt hvzero.le
  have hlogthree :
      Real.log (Real.sqrt (3 : ℝ)) = Real.log 3 / 2 :=
    Real.log_sqrt (by positivity)
  have hchildentropy :
      Real.binEntropy v =
        -v * Real.log v - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hleft :
      (((1 - q) ^ 2 *
          (Real.binEntropy z₀₀ +
            (1 - z₀₀) * Real.log a + z₀₀ * Real.log (b / 3)) +
        ((1 - q) * q) *
          (Real.binEntropy z₀₁ +
            (1 - z₀₁) * Real.log (a / Real.sqrt 3) +
              z₀₁ * Real.log (b / Real.sqrt 3))) +
        (q * (1 - q)) *
          (Real.binEntropy z₁₀ +
            (1 - z₁₀) * Real.log (a / Real.sqrt 3) +
              z₁₀ * Real.log (b / Real.sqrt 3))) +
        q ^ 2 *
          (Real.binEntropy z₁₁ +
            (1 - z₁₁) * Real.log (a / 3) + z₁₁ * Real.log b) =
        kernel.conditionalEntropy * Real.log 2 -
          Real.binEntropy v / 2 -
          Real.log 3 * kernel.averageDisagreement := by
    rw [hentropy, hdisagreement, hchildentropy,
      Real.log_div hb.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div ha.ne' hthree.ne',
      Real.log_div hb.ne' hthree.ne',
      Real.log_div ha.ne' (by norm_num : (3 : ℝ) ≠ 0),
      hloga, hlogb, hlogthree]
    linear_combination
      ((Real.log (1 - v) - Real.log v) / 2) * hmarginal
  have hright :
      (((1 - q) ^ 2 * Real.log (a + b / 3) +
        ((1 - q) * q) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        (q * (1 - q)) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        q ^ 2 * Real.log (a / 3 + b) =
        binaryConditionalLogPotential q a b - Real.binEntropy q / 2 := by
    have hmixed :
        a / Real.sqrt 3 + b / Real.sqrt 3 =
          (a + b) / Real.sqrt 3 := by ring
    rw [hmixed]
    unfold binaryConditionalLogPotential
    ring
  rw [hleft, hright] at hcombined
  simpa [q, v, a, b] using hcombined
end TwoDegenerateGraphs.BinaryPairKernel
