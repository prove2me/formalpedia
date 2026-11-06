-- Prove2me | solution 1 for RH.Transport.Certificate.candidate_matches_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:26:52.151582+00:00
-- url     : https://prove2.me/submissions/f40e8cea-e28d-455a-870f-630da2b1ed14

import Definitions.Def_Transport_Candidate
import Definitions.Def_Transport_Endpoint
import Definitions.Def_Transport_Certificate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Certificate
noncomputable section
namespace RH.Transport.Certificate
theorem _root_.solution :
    Candidate.p = Endpoint.perturbation ∧
    Candidate.B = Endpoint.boundary ∧
    Candidate.cushion = Endpoint.saving := by
  norm_num [Candidate.p, Candidate.B, Candidate.cushion, Geometry.boundary,
    Endpoint.perturbation, Endpoint.boundary, Endpoint.saving]
end RH.Transport.Certificate
