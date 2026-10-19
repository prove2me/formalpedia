-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.conditionalEntropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/c97b4bcd-3b4e-4e53-ae65-18039328e218

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_nonneg
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_childMarginal_le_one
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothed_childMarginal
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothed_averageDisagreement
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothedConditionalEntropy_continuous
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothed_conditionalEntropy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_conditionalEntropy_bound_of_marginal_interior

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by
    dsimp [mixing]
    positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryPairKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto :
      Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have hnonnegative := mul_nonneg
      (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have hpositive := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left
      (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero :
        smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := by
    rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          kappa + logTwo 3 * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (kappa + logTwo 3 * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hdisagreement_term :=
      (tendsto_const_nhds (x := logTwo 3)).mul hdisagreement_tendsto
    have hentropy_term :=
      (hchildentropy_tendsto.sub
        (tendsto_const_nhds (x :=
          binaryEntropy kernel.parentProbability))).div_const 2
    have hsum :=
      (tendsto_const_nhds (x := kappa)).add
        (hdisagreement_term.add hentropy_term)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto'
    hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)
end TwoDegenerateGraphs.BinaryPairKernel
