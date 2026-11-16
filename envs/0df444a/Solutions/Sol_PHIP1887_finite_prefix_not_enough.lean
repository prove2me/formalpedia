-- Prove2me | solution 1 for PHIP1887.finite_prefix_not_enough
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:48.389421+00:00
-- url     : https://prove2.me/submissions/fb7ae36a-66c4-4ff5-9732-2eba6fc7d83c

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (N : ℕ) :
    ∃ Q : ℕ → ℝ → ℝ,
      (∀ k, k ≤ N → PositiveAt Q k) ∧
      (∀ k, N < k → NegativeAt Q k) := by
  refine ⟨fun k _ => if k ≤ N then 1 else -1, ?_, ?_⟩
  · intro k hk x hx
    simp [hk]
  · intro k hk
    refine ⟨1, by norm_num, ?_⟩
    simp [show ¬k ≤ N by omega]
