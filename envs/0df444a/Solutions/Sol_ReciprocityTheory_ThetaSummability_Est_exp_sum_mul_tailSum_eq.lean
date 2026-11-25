-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.exp_sum_mul_tailSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:24:11.977823+00:00
-- url     : https://prove2.me/submissions/8f51822b-b51e-4d61-bba4-326517072417

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeExp
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_sum_mul_tailSum

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
theorem _root_.solution (s : Fin r → ℝ) :
    (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) =
      fun y => ∏ k, (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) k (y k) := by
  funext y
  rw [sum_mul_tailSum, Real.exp_sum]
end ReciprocityTheory.ThetaSummability.Est
