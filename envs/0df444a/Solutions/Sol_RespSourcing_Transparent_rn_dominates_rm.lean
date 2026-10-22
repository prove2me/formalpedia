-- Prove2me | solution 1 for RespSourcing.Transparent.rn_dominates_rm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:35.053996+00:00
-- url     : https://prove2.me/submissions/bb016609-740b-4b3d-b80e-7b07ef3d5ed5

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing)
    (hθ : 0 < p.θ)
    (hr : (p.v - p.cR) * ((1 - p.θ) / p.θ) < p.r) :
    profit p .RM < profit p .RN := by
  have h1 : (p.v - p.cR) * (1 - p.θ) < p.r * p.θ := by
    have := mul_lt_mul_of_pos_right hr hθ
    have e : (p.v - p.cR) * ((1 - p.θ) / p.θ) * p.θ = (p.v - p.cR) * (1 - p.θ) := by
      field_simp
    linarith
  simp only [profit]
  nlinarith [h1]
