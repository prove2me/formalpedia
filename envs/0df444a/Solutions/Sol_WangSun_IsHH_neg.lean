-- Prove2me | solution 1 for WangSun.IsHH_neg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:41:11.072028+00:00
-- url     : https://prove2.me/submissions/b2d1533e-bcca-41fc-8882-cf6373e7864f

import Definitions.Def_WangSunCPWL

open Finset

variable {n : ℕ}

private theorem isHinge_neg {h : (Fin n → ℝ) → ℝ} (hh : IsHinge h) : IsHinge (-h) := by
  obtain ⟨σ, L, hσ, rfl⟩ := hh
  refine ⟨-σ, L, ?_, ?_⟩
  · rcases hσ with h | h <;> simp [h]
  · funext x
    simp

theorem solution {f : (Fin n → ℝ) → ℝ} (hf : IsHH f) : IsHH (-f) := by
  obtain ⟨K, h, hh, rfl⟩ := hf
  exact ⟨K, fun k => -(h k), fun k => isHinge_neg (hh k), by simp⟩
