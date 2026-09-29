-- Prove2me | solution 1 for SmaleNinth.feasible_iff_positive_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T07:45:57.922423+00:00
-- url     : https://prove2.me/submissions/8b54b7bb-11f8-4333-bfcb-3ecbb3e8814e

import Definitions.Def_Polyhedron
import Theorems.Thm_SmaleNinth_lp_strong_duality
import Theorems.Thm_SmaleNinth_lp_complementary_slackness

open Matrix LinearOptimization SmaleNinth

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
        x ∈ polyhedron A b ∧
        (∀ i, 0 ≤ y i) ∧
        (∀ k, ∑ i, y i * A i k = 0) ∧
        (∀ i, y i * ((A.mulVec x) i - b i) = 0) := by
  constructor
  · intro h
    obtain ⟨x, y, hx, hy, hyA, hobj, hopt⟩ :=
      SmaleNinth.lp_strong_duality A b (fun _ => 0) h ⟨0, by
        intro x' hx'
        simp⟩
    refine ⟨x, y, hx, hy, ?_, ?_⟩
    · intro k
      simpa using hyA k
    · have hcs :=
        (SmaleNinth.lp_complementary_slackness A b (fun _ => 0) hx hy hyA).mp hobj
      simpa using hcs
  · rintro ⟨x, y, hx, _, _, _⟩
    exact ⟨x, hx⟩
