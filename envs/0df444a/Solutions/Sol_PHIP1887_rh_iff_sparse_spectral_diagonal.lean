-- Prove2me | solution 1 for PHIP1887.rh_iff_sparse_spectral_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:14:24.346204+00:00
-- url     : https://prove2.me/submissions/e14888f4-3b55-4a7a-9e7a-b5a64a6c3382

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_recurrence_and_minimum_propagate
import Theorems.Thm_PHIP1887_sparse_equivalence
import Theorems.Thm_PHIP1887_rh_spectral_tower_nonneg
open MeasureTheory Set
open PHIP1887

theorem solution
    (rho : ℕ → ℂ) (S : Set ℕ)
    (hS : Cofinal S)
    (hzero : ∀ j, riemannZeta (rho j) = 0)
    (htrivial : ∀ j, ¬ ∃ n : ℕ, rho j = -2*((n:ℂ)+1))
    (hone : ∀ j, rho j ≠ 1)
    (him : ∀ j, (rho j).im ≠ 0)
    (hs : ∀ k ∈ S, ∀ x, 0 < x → Summable (fun j =>
      (atom (zeroCoordinate x (rho j)) k k).re))
    (hentry : ¬ RiemannHypothesis →
      ∃ K, 1 ≤ K ∧ NegativeAt (spectralDiagonal rho) K)
    (curvature : ℕ → ℝ → ℝ)
    (hrec : ∀ k x, 1 ≤ k → 0 < x →
      curvature k x = (k:ℝ)^2*spectralDiagonal rho k x -
        2*(k:ℝ)*(2*(k:ℝ)+1)*spectralDiagonal rho (k+1) x)
    (hmin : ∀ k, 1 ≤ k → NegativeAt (spectralDiagonal rho) k →
      ∃ x, 0 < x ∧ spectralDiagonal rho k x < 0 ∧ 0 ≤ curvature k x) :
    RiemannHypothesis ↔ ∀ k ∈ S, PositiveAt (spectralDiagonal rho) k := by
  apply sparse_equivalence RiemannHypothesis (spectralDiagonal rho) S hS
  · intro hRH k hk x hx
    exact rh_spectral_tower_nonneg rho x k k hRH hzero htrivial hone him hx (hs k hk x hx)
  · exact hentry
  · exact recurrence_and_minimum_propagate _ curvature hrec hmin
