-- Prove2me | solution 1 for PHIP1887.negative_tail
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:47:22.581076+00:00
-- url     : https://prove2.me/submissions/16f63c81-5427-4747-804c-d1858c237c39

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
open MeasureTheory Set
open PHIP1887

theorem solution (Q : ℕ → ℝ → ℝ)
    (hstep : ∀ k, 1 ≤ k → NegativeAt Q k → NegativeAt Q (k+1))
    (K : ℕ) (hK : 1 ≤ K) (hseed : NegativeAt Q K) :
    ∀ k, K ≤ k → NegativeAt Q k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hseed
  | succ n hn ih => exact hstep n (le_trans hK hn) ih
