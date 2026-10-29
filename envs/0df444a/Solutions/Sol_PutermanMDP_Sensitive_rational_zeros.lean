-- Prove2me | solution 1 for PutermanMDP.Sensitive.rational_zeros
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:04:41.51679+00:00
-- url     : https://prove2.me/submissions/dec2934a-b252-480b-85e3-a6077f1c9b84

import Mathlib

theorem solution (I : Set ℝ) (hI : Set.OrdConnected I) (f : ℝ → ℝ)
    (hf : ∃ p q : Polynomial ℝ, (∀ x ∈ I, q.eval x ≠ 0) ∧
      ∀ x ∈ I, f x = p.eval x / q.eval x)
    (hzero : ∃ x ∈ I, f x = 0) :
    (∀ x ∈ I, f x = 0) ∨ {x : ℝ | x ∈ I ∧ f x = 0}.Finite := by
  obtain ⟨p, q, hq, hfpq⟩ := hf
  by_cases hp : p = 0
  · left; intro x hx; rw [hfpq x hx, hp]; simp
  · right
    apply (p.rootSet ℝ).toFinite.subset
    rintro x ⟨hx, hfx⟩
    rw [hfpq x hx, div_eq_zero_iff] at hfx
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    exact hfx.resolve_right (hq x hx)
