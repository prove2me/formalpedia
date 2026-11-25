-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KE.norm_eval_sub_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:39.335162+00:00
-- url     : https://prove2.me/submissions/c1c9c154-87f5-4ad8-9ea5-c297b5d760f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_pow_sub_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1.KE
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by
        gcongr
        · exact hP i
        · exact norm_pow_sub_pow_le hx hy i
    _ = _ := one_mul _
end ReciprocityTheory.ChartRestriction.L1.KE
