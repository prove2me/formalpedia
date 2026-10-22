-- Prove2me | solution 1 for RespSourcing.Transparent.ds_vs_rm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:09.579362+00:00
-- url     : https://prove2.me/submissions/c218d218-b7b0-4a04-9e37-0d310bb9daa2

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing) :
    (profit p .RM < profit p .DS ↔
      p.φ * (p.cVP + p.α * p.θ * (p.v + p.r - p.cR)) <
        p.θ * p.r + (1 - p.θ) * p.Δ) := by
  simp only [profit, Params.Δ]
  constructor <;> intro h <;> nlinarith [h]
