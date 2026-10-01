-- Prove2me | solution 1 for ShiQMACenteredGap.approximate_centering
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T09:11:58.279142+00:00
-- url     : https://prove2.me/submissions/f54760be-07c9-4ef1-bc52-4cc08c7601ea

import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution {a b u : ℝ}
    (hu : |u - centeringCoin a b| ≤ (a - b) / 4) :
    (∀ t : ℝ, a ≤ t → 1 / 2 + (a - b) / 8 ≤ centeredAcceptance u t) ∧
    (∀ t : ℝ, t ≤ b → centeredAcceptance u t ≤ 1 / 2 - (a - b) / 8) := by
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  dsimp [centeringCoin] at hl hr
  constructor
  · intro t ht
    dsimp [centeredAcceptance]
    linarith
  · intro t ht
    dsimp [centeredAcceptance]
    linarith
