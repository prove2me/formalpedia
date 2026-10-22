-- Prove2me | solution 1 for RespSourcing.Transparent.lc_vs_rm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:25.042789+00:00
-- url     : https://prove2.me/submissions/69abe8e5-a352-42e5-9eec-121737ec9de7

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing) :
    (profit p .RM < profit p .LC ↔
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) < p.Δ) := by
  simp only [profit, Params.Δ]
  constructor <;> intro h <;> nlinarith [h]
