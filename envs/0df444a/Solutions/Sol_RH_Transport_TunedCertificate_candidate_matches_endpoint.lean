-- Prove2me | solution 1 for RH.Transport.TunedCertificate.candidate_matches_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:30.169086+00:00
-- url     : https://prove2.me/submissions/131e60ce-02b2-41eb-ac1d-2517b12e4c57

import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_Transport_TunedEndpoint
import Definitions.Def_Transport_Certificate
import Definitions.Def_Transport_TunedCertificate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCertificate
noncomputable section
namespace RH.Transport.TunedCertificate
theorem _root_.solution :
    TunedCandidate.p = TunedEndpoint.perturbation ∧
    TunedCandidate.b = TunedEndpoint.b ∧
    TunedCandidate.B = TunedEndpoint.boundary ∧
    TunedCandidate.ell = TunedEndpoint.ell ∧
    TunedCandidate.ly = TunedEndpoint.ly ∧
    TunedCandidate.h = TunedEndpoint.h ∧
    TunedCandidate.cushion = TunedEndpoint.saving := by
  norm_num [TunedCandidate.p, TunedCandidate.b, TunedCandidate.B,
    TunedCandidate.boundaryAt, TunedCandidate.ell, Geometry.ell,
    TunedCandidate.ly, TunedCandidate.lyAt, TunedCandidate.h, TunedCandidate.hAt,
    TunedCandidate.cushion, TunedEndpoint.perturbation, TunedEndpoint.b,
    TunedEndpoint.boundary, TunedEndpoint.ell, TunedEndpoint.ly, TunedEndpoint.h,
    TunedEndpoint.saving]
end RH.Transport.TunedCertificate
