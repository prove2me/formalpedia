-- Prove2me | solution 1 for TwoDegenerateGraphs.BinaryPairKernel.conditionalEntropy_bound_of_marginal_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/5315ca91-c79b-4f47-8397-5e4a953e4498

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryConditionalLogPotential_le_kappa
import Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_conditionalEntropy_logsum_reduction

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel
namespace TwoDegenerateGraphs.BinaryPairKernel
theorem _root_.solution
    (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hzeroAmplitude :
      0 ≤ Real.sqrt (1 - kernel.childMarginal) :=
    Real.sqrt_nonneg _
  have honeAmplitude : 0 ≤ Real.sqrt kernel.childMarginal :=
    Real.sqrt_nonneg _
  have hamplitudes :
      Real.sqrt (1 - kernel.childMarginal) ^ 2 +
          Real.sqrt kernel.childMarginal ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_pos.mpr hmarginal_one).le,
      Real.sq_sqrt hmarginal_zero.le]
    ring
  have hpotential := binaryConditionalLogPotential_le_kappa
    kernel.parentProbability
    (Real.sqrt (1 - kernel.childMarginal))
    (Real.sqrt kernel.childMarginal)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hzeroAmplitude honeAmplitude hamplitudes
  have hreduction := conditionalEntropy_logsum_reduction kernel
    hmarginal_zero hmarginal_one
  have hright :
      (kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        kappa * Real.log 2 +
          Real.log 3 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy logTwo
    field_simp [log_two_pos.ne']
  have hscaled :
      kernel.conditionalEntropy * Real.log 2 ≤
        (kappa + logTwo 3 * kernel.averageDisagreement +
          (binaryEntropy kernel.childMarginal -
            binaryEntropy kernel.parentProbability) / 2) * Real.log 2 := by
    rw [hright]
    linarith
  exact (mul_le_mul_iff_of_pos_right log_two_pos).mp hscaled
end TwoDegenerateGraphs.BinaryPairKernel
