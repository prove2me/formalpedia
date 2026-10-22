-- Prove2me | solution 1 for RespSourcing.Transparent.ds_vs_rn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:14.956803+00:00
-- url     : https://prove2.me/submissions/4d5f3e78-3ff4-4474-b176-bb3bb6fffbf4

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing) :
    (profit p .RN < profit p .DS ↔
      p.φ * (p.cVP + p.α * p.θ * (p.v + p.r - p.cR)) <
        (1 - p.θ) * (p.v - p.cNR)) := by
  simp only [profit]
  constructor <;> intro h <;> nlinarith [h]
