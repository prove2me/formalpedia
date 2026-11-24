-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.isCoprime_lin
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T06:01:55.781211+00:00
-- url     : https://prove2.me/submissions/be38c27d-eae3-46a2-9714-ccaab0355284

import Mathlib
open Polynomial


theorem solution (α β γ : ℂ) (h : β - γ * α ≠ 0) : IsCoprime (X - C α) (C β - C γ * X) := by
  let d := β - γ * α
  have hd : d ≠ 0 := h
  refine ⟨C d⁻¹ * C γ, C d⁻¹, ?_⟩
  calc
    _ = C d⁻¹ * (C β - C γ * C α) := by ring
    _ = C (d⁻¹ * d) := by simp [d]
    _ = 1 := by simp [hd]
