-- Prove2me | solution 1 for RespSourcing.Transparent.lc_vs_rn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:30.50568+00:00
-- url     : https://prove2.me/submissions/a4950160-3ca0-4189-96d7-c5169efb1a89

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing) :
    (profit p .RN < profit p .LC ↔
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) <
        (p.v - p.cNR) - p.θ * (p.v + p.r - p.cR)) := by
  simp only [profit]
  constructor <;> intro h <;> nlinarith [h]
