-- Prove2me | solution 1 for RH.Transport.Certificate.buffered_high_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:50.689361+00:00
-- url     : https://prove2.me/submissions/e2c73ba4-da78-41d9-a012-50d693a420b5

import Definitions.Def_Transport_Candidate
import Definitions.Def_Transport_Endpoint
import Definitions.Def_Transport_Certificate
import Theorems.Thm_RH_Transport_Certificate_row_slope_bounds
import Theorems.Thm_RH_Transport_Certificate_high_exponent_endpoint
import Theorems.Thm_RH_Transport_Candidate_zeta_pos
import Theorems.Thm_RH_Transport_Endpoint_adaptive_endpoint_bound


set_option autoImplicit false
open RH RH.Transport RH.Transport.Certificate
noncomputable section
namespace RH.Transport.Certificate
theorem _root_.solution {d δ x : ℝ}
    (hd : d ≤ Geometry.h Candidate.p + Candidate.zeta)
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    highExponent d δ x ≤ -(3 / 160000000000 : ℝ) := by
  have he := Endpoint.adaptive_endpoint_bound hdlo hdhi hxlo hxhi
  obtain ⟨hs0, hs2⟩ := row_slope_bounds hdlo hdhi hxlo hxhi
  have hm := mul_le_mul_of_nonneg_right
    (show d - Geometry.h Candidate.p ≤ Candidate.zeta by linarith) hs0
  have hz := mul_le_mul_of_nonneg_left hs2 Candidate.zeta_pos.le
  rw [high_exponent_endpoint]
  norm_num [Candidate.zeta] at hm hz
  linarith
end RH.Transport.Certificate
