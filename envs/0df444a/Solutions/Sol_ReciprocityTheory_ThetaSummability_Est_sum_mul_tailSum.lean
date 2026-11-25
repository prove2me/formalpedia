-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.sum_mul_tailSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:44.328178+00:00
-- url     : https://prove2.me/submissions/bb620485-5e82-41f4-b864-fc7623ffc686

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ThetaSummability ReciprocityTheory.ThetaSummability.Est
open MeasureTheory Finset Real
variable {r : ℕ}
namespace ReciprocityTheory.ThetaSummability.Est
theorem _root_.solution (s y : Fin r → ℝ) :
    ∑ i, s i * tailSum y i = ∑ k, partialSum s k * y k := by
  simp only [tailSum, partialSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
end ReciprocityTheory.ThetaSummability.Est
