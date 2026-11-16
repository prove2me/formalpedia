-- Prove2me | solution 1 for PHIP1887.cofinal_positivity_from_errors
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:30.944867+00:00
-- url     : https://prove2.me/submissions/496678a1-e86e-432d-9f79-4246b9e7f5fd

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution
    (Q : ℕ → ℝ → ℝ) (S : Set ℕ)
    (hcert : ∀ k ∈ S, ∀ x, 0 < x → ∀ ε : ℝ, 0 < ε → -ε ≤ Q k x) :
    ∀ k ∈ S, PositiveAt Q k := by
  intro k hk x hx
  by_contra hn
  have hq : Q k x < 0 := lt_of_not_ge hn
  have hh := hcert k hk x hx (-Q k x / 2) (by linarith)
  linarith
