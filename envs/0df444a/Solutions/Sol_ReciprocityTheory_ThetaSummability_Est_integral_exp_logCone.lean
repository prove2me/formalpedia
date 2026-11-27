-- Prove2me | solution 1 for ReciprocityTheory.ThetaSummability.Est.integral_exp_logCone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:19.156104+00:00
-- url     : https://prove2.me/submissions/4c89c4d9-158f-4874-9290-cdde353c4052

import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeChange
import Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_ConeExp
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_exp_sum_mul_tailSum_eq
import Theorems.Thm_ReciprocityTheory_ThetaSummability_Est_setIntegral_logCone


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
theorem _root_.solution (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    ∫ x in logCone r c, exp (∑ i, s i * x i) =
      ∏ k, exp (partialSum s k * c) / (-partialSum s k) := by
  rw [setIntegral_logCone]
  show ∫ y in lowerBox r c, (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) y = _
  rw [exp_sum_mul_tailSum_eq, lowerBox, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (hs k), neg_div, div_neg]
end ReciprocityTheory.ThetaSummability.Est
