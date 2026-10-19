-- Prove2me | solution 1 for TwoDegenerateGraphs.empiricalConditionalEntropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/97ec3826-1706-47fd-a389-fe54be9693be

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_conditionalEntropy_bound
import Theorems.Thm_TwoDegenerateGraphs_empiricalConditionalEntropy_error
import Theorems.Thm_TwoDegenerateGraphs_empiricalAverageDisagreement_error
import Theorems.Thm_TwoDegenerateGraphs_empiricalChildMarginal_entropy_error

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hconditional := empiricalConditionalEntropy_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hdisagreement := empiricalAverageDisagreement_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmarginal := empiricalChildMarginal_entropy_error
    parentCount oneCount hparents hones kernel hparameter
  have hindependent := BinaryPairKernel.conditionalEntropy_bound kernel
  have hconditional_upper :
      empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hconditional).2
    linarith
  have hdisagreement_upper :
      kernel.averageDisagreement ≤
        empiricalAverageDisagreement parentCount oneCount kernel +
          1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hdisagreement).1
    linarith
  have hdisagreement_scaled := mul_le_mul_of_nonneg_left
    hdisagreement_upper logTwo_three_pos.le
  have hmarginal_upper :
      binaryEntropy kernel.childMarginal ≤
        binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) +
          binaryEntropy (1 / (parentCount : ℝ)) := by
    have h := (abs_le.mp hmarginal).1
    linarith
  have herror :
      1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2 =
        empiricalEntropyError parentCount := by
    unfold empiricalEntropyError
    ring
  calc
    empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) :=
      hconditional_upper
    _ ≤ kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        (1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2) := by
      nlinarith
    _ = kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
      rw [herror]
end TwoDegenerateGraphs
