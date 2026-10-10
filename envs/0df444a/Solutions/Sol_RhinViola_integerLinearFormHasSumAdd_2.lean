-- Prove2me | solution 2 for RhinViola.integerLinearFormHasSumAdd
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:05:22.361034+00:00
-- url     : https://prove2.me/submissions/42a315e0-9462-4604-9297-77dc8dac6197

import Mathlib.Tactic

theorem solution
    (α : ℝ) (f g : ℕ → ℝ) (z₁ z₂ c₁ c₂ : ℤ)
    (hf : HasSum f ((z₁ : ℝ) + (c₁ : ℝ) * α))
    (hg : HasSum g ((z₂ : ℝ) + (c₂ : ℝ) * α)) :
    HasSum (fun k : ℕ => f k + g k)
      (((z₁ + z₂ : ℤ) : ℝ) + (((c₁ + c₂ : ℤ) : ℝ) * α)) := by
  have h := hf.add hg
  convert h using 1
  push_cast
  ring
