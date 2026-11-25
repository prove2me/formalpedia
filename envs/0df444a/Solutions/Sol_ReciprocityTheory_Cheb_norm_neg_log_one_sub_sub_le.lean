-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_neg_log_one_sub_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:39.068886+00:00
-- url     : https://prove2.me/submissions/6064fdfa-22d5-4a85-bb95-c86113fa27f2

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeSum

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
theorem _root_.solution {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le h1
  rw [norm_neg] at h
  have e : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by ring_nf
  rw [e, norm_neg]
  refine h.trans ?_
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring
end ReciprocityTheory.Cheb
