-- Prove2me | solution 1 for PHIP1887.strictly_increasing_range_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:39.623744+00:00
-- url     : https://prove2.me/submissions/ad89ca36-3b55-419e-921e-c20e63e4da73

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (a : ℕ → ℕ)
    (h : ∀ n, a n < a (n+1)) : Cofinal (Set.range a) := by
  intro K
  have hg : ∀ n, n ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have hh := h n; omega
  exact ⟨a K, ⟨K, rfl⟩, hg K⟩
