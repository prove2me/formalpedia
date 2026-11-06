-- Prove2me | solution 1 for RH.Transport.TunedEndpoint.certificate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:36.239085+00:00
-- url     : https://prove2.me/submissions/c59a4d99-4fa3-4258-9992-06816759f3f0

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section
namespace RH.Transport.TunedEndpoint
theorem _root_.solution (δ x : ℝ) (hJ : countDenominator δ x ≠ 0) :
    certificatePolynomial δ x =
      (-endpointExponent δ x - saving) * countDenominator δ x := by
  unfold certificatePolynomial endpointExponent boundary ly h saving
  unfold ell perturbation b
  simp only [adaptiveCount, Endpoint.adaptiveCount]
  field_simp
  unfold countDenominator Endpoint.countDenominator at *
  field_simp at *
  ring
end RH.Transport.TunedEndpoint
