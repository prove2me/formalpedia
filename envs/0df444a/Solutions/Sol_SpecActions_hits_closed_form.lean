-- Prove2me | solution 1 for SpecActions.hits_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @naimengye
-- created : 2026-09-11T15:36:59.534988+00:00
-- url     : https://prove2.me/submissions/f3f4c065-5b8b-4af4-9194-e88ac4cc6839

import Definitions.Def_SpecActions_model

open SpecActions

/-- Closed form for the two-term hit-count recursion
`S 0 = 0`, `S 1 = p`, `S (n+2) = p (1 + S n) + (1 - p) S (n+1)`. -/
theorem solution (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    hits p n = p / (1 + p) * n + p ^ 2 / (1 + p) ^ 2 * (1 - (-p) ^ n) := by
  have hpos : (0:ℝ) < 1 + p := by linarith
  have hne : (1:ℝ) + p ≠ 0 := ne_of_gt hpos
  -- Carry the statement and its successor together, so that ordinary
  -- induction supplies both values the two-term recursion consumes.
  suffices h : ∀ m : ℕ,
      hits p m = p / (1 + p) * (m : ℝ) + p ^ 2 / (1 + p) ^ 2 * (1 - (-p) ^ m) ∧
      hits p (m + 1)
        = p / (1 + p) * ((m + 1 : ℕ) : ℝ)
            + p ^ 2 / (1 + p) ^ 2 * (1 - (-p) ^ (m + 1)) from (h n).1
  intro m
  induction m with
  | zero =>
    -- `S 0 = 0` and `S 1 = p`; the latter needs `p/(1+p) + p²/(1+p)²·(1+p) = p`.
    refine ⟨by simp [hits], ?_⟩
    show hits p 1 = _
    simp only [hits]
    field_simp
    ring
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    -- One step of the recursion, with both predecessors rewritten to closed form.
    show hits p (k + 2) = _
    simp only [hits]
    rw [ih0, ih1]
    push_cast
    field_simp
    ring
