-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_log_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:55.094625+00:00
-- url     : https://prove2.me/submissions/841af154-c5d1-41dc-a056-c34d7a478bf0

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  rw [show -Real.log (1 - x) - x = -(x + Real.log (1 - x)) by ring, abs_neg]
  calc |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
end ReciprocityTheory.Cheb
