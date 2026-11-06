-- Prove2me | solution 1 for RH.Transport.Endpoint.certificate_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:25:11.674782+00:00
-- url     : https://prove2.me/submissions/06c74869-7f60-4235-9069-a5dd381fc09c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution (δ x : ℝ) (hJ : countDenominator δ x ≠ 0) :
    certificatePolynomial δ x =
      (-endpointExponent δ x - saving) * countDenominator δ x := by
  unfold certificatePolynomial endpointExponent adaptiveCount boundary ell ly h
    saving perturbation
  field_simp
  unfold countDenominator at *
  field_simp at *
  ring
end RH.Transport.Endpoint
