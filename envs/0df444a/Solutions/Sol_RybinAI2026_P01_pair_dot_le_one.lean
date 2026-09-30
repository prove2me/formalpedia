-- Prove2me | solution 1 for RybinAI2026.P01.pair_dot_le_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:46:15.271691+00:00
-- url     : https://prove2.me/submissions/195febff-715e-4e81-aea7-961d8b1cd6bc

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {r₁ r₂ s₁ s₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hr : r₁ ^ 2 + r₂ ^ 2 ≤ 1)
    (hs : s₁ ^ 2 + s₂ ^ 2 ≤ 1) :
    r₁ * s₁ + r₂ * s₂ ≤ 1 := by
  nlinarith [sq_nonneg (r₁ - s₁), sq_nonneg (r₂ - s₂)]
