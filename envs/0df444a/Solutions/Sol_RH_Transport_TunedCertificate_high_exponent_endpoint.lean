-- Prove2me | solution 1 for RH.Transport.TunedCertificate.high_exponent_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:31.783144+00:00
-- url     : https://prove2.me/submissions/61016ea7-e520-4b81-b7b4-463e64eec355

import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_Transport_TunedEndpoint
import Definitions.Def_Transport_Certificate
import Definitions.Def_Transport_TunedCertificate
import Theorems.Thm_RH_Transport_TunedCertificate_candidate_matches_endpoint
import Theorems.Thm_RH_Transport_Certificate_candidate_matches_endpoint


set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCertificate
noncomputable section
namespace RH.Transport.TunedCertificate
theorem _root_.solution (d δ x : ℝ) :
    highExponent d δ x = TunedEndpoint.endpointExponent δ x +
      (d - TunedCandidate.h) * Certificate.rowSlope δ x := by
  obtain ⟨_, _, hB, hell, hly, hh, _⟩ := candidate_matches_endpoint
  unfold highExponent TunedEndpoint.endpointExponent Certificate.rowSlope
  rw [hB, hell, hly, hh]
  simp only [TunedEndpoint.adaptiveCount]
  ring
end RH.Transport.TunedCertificate
