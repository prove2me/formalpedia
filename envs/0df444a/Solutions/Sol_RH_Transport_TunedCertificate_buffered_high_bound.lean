-- Prove2me | solution 1 for RH.Transport.TunedCertificate.buffered_high_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:29.133768+00:00
-- url     : https://prove2.me/submissions/cc5e3bf8-9ef3-4c9c-85e5-22cc1042df7b

import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_Transport_TunedEndpoint
import Definitions.Def_Transport_Certificate
import Definitions.Def_Transport_TunedCertificate
import Theorems.Thm_RH_Transport_TunedCertificate_high_exponent_endpoint
import Theorems.Thm_RH_Transport_Candidate_zeta_pos
import Theorems.Thm_RH_Transport_Certificate_high_exponent_endpoint
import Theorems.Thm_RH_Transport_Certificate_row_slope_bounds
import Theorems.Thm_RH_Transport_Endpoint_adaptive_endpoint_bound
import Theorems.Thm_RH_Transport_TunedCandidate_zeta_pos
import Theorems.Thm_RH_Transport_TunedEndpoint_adaptive_endpoint_bound


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCertificate
noncomputable section
namespace RH.Transport.TunedCertificate
theorem _root_.solution {d δ x : ℝ}
    (hd : d ≤ TunedCandidate.h + TunedCandidate.zeta)
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    highExponent d δ x ≤ -(3 / 4000000000000 : ℝ) := by
  have he := TunedEndpoint.adaptive_endpoint_bound hdlo hdhi hxlo hxhi
  obtain ⟨hs0, hs2⟩ := Certificate.row_slope_bounds hdlo hdhi hxlo hxhi
  have hm := mul_le_mul_of_nonneg_right
    (show d - TunedCandidate.h ≤ TunedCandidate.zeta by linarith) hs0
  have hz := mul_le_mul_of_nonneg_left hs2 TunedCandidate.zeta_pos.le
  rw [high_exponent_endpoint]
  norm_num [TunedCandidate.zeta] at hm hz
  linarith
end RH.Transport.TunedCertificate
