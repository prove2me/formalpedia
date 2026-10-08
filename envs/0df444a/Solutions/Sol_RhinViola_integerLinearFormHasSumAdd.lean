-- Prove2me | solution 1 for RhinViola.integerLinearFormHasSumAdd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T09:23:11.53673+00:00
-- url     : https://prove2.me/submissions/416f7d9d-945b-40e3-92c2-c61fcd2fa3c7

import Mathlib.Tactic

theorem solution
    (α : ℝ) (f g : ℕ → ℝ) (z₁ z₂ c₁ c₂ : ℤ)
    (hf : HasSum f ((z₁ : ℝ) + (c₁ : ℝ) * α))
    (hg : HasSum g ((z₂ : ℝ) + (c₂ : ℝ) * α)) :
    HasSum (fun k : ℕ => f k + g k)
      (((z₁ + z₂ : ℤ) : ℝ) + (((c₁ + c₂ : ℤ) : ℝ) * α)) := by
  have hsum :
      ((z₁ : ℝ) + (c₁ : ℝ) * α) +
          ((z₂ : ℝ) + (c₂ : ℝ) * α) =
        (((z₁ + z₂ : ℤ) : ℝ) + (((c₁ + c₂ : ℤ) : ℝ) * α)) := by
    push_cast
    ring
  rw [← hsum]
  exact hf.add hg
