-- Prove2me | solution 1 for PHIP1887.cofinal_positivity_excludes_seed
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:53:48.676575+00:00
-- url     : https://prove2.me/submissions/0d0764fa-3e35-4617-9a72-96f29ea92664

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_negative_tail
open MeasureTheory Set
open PHIP1887

theorem solution (Q : ℕ → ℝ → ℝ) (S : Set ℕ)
    (hS : Cofinal S)
    (hpos : ∀ k ∈ S, PositiveAt Q k)
    (hstep : ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1)) :
    ¬ ∃ K, 1 ≤ K ∧ NegativeAt Q K := by
  rintro ⟨K, hK, hneg⟩
  obtain ⟨k, hkS, hKk⟩ := hS K
  obtain ⟨x, hx, hqx⟩ := negative_tail Q hstep K hK hneg k hKk
  exact (not_lt_of_ge (hpos k hkS x hx)) hqx
