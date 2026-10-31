-- Prove2me | solution 1 for RefugeeCash.PDCA.refugee_profit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:40:24.313622+00:00
-- url     : https://prove2.me/submissions/1b873318-7f3c-4153-8039-07ca5eacc9be

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model
open RefugeeCash.PDCA

theorem solution(P : Params) (p k : ℝ) (hp : p ≠ 0) :
    P.c * refugeeDemand P p k = k * P.B * P.c / p ∧
      piR P p k = k * P.B * (1 - P.c / p) := by
  unfold piR refugeeDemand
  constructor <;> field_simp <;> ring
