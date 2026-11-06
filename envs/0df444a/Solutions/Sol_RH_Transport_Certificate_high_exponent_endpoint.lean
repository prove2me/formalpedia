-- Prove2me | solution 1 for RH.Transport.Certificate.high_exponent_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:38.462263+00:00
-- url     : https://prove2.me/submissions/2653bcf1-b26d-4dc7-af81-653d6e06235c

import Definitions.Def_Transport_Candidate
import Definitions.Def_Transport_Endpoint
import Definitions.Def_Transport_Certificate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Certificate
noncomputable section
namespace RH.Transport.Certificate
theorem _root_.solution (d δ x : ℝ) :
    highExponent d δ x = Endpoint.endpointExponent δ x +
      (d - Geometry.h Candidate.p) * rowSlope δ x := by
  unfold highExponent Endpoint.endpointExponent rowSlope
  unfold Candidate.B Candidate.p Geometry.boundary Geometry.h Geometry.ly Geometry.ell
  simp only [Endpoint.boundary, Endpoint.h, Endpoint.ly, Endpoint.ell, Endpoint.perturbation]
  ring
end RH.Transport.Certificate
