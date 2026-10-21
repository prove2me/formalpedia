-- Prove2me | solution 1 for SkillData.GoldRush.eq_C5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:09:46.029109+00:00
-- url     : https://prove2.me/submissions/374c48e0-efc7-4dd0-9a30-e24e8463c210

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush
end SkillData.GoldRush
open SkillData.GoldRush

theorem solution (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (c τη : ℝ)
    (X : Clarity) (lam α : ℝ) (hF : Feasible P C c τη X lam α) :
    profit P τη X lam α = P.β * lam * C c lam / (1 - P.β) := by
  obtain ⟨-, -, -, -, hβ1, -, -⟩ := hP
  have hne : (1 - P.β) ≠ 0 := by linarith
  cases X with
  | finite x =>
    obtain ⟨-, -, -, -, -, h⟩ := hF
    simp only [profit]
    rw [← h]; field_simp
  | asIs =>
    obtain ⟨-, -, -, -, h⟩ := hF
    simp only [profit]
    rw [← h]; field_simp
