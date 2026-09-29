-- Prove2me | solution 1 for buchholz_matched_walk_sum_le_pair_count_row_column_energy_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T03:01:37.390728+00:00
-- url     : https://prove2.me/submissions/08c54117-d754-4e12-ac2a-6209e5e612c5

import Theorems.Thm_buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
import Theorems.Thm_buchholz_pairing_count_eq_factorial_ratio

open MatrixCompletion
open scoped BigOperators

/-- Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 25.  The sketch
separates Buchholz's matched-walk domination by pair partitions from the
enumerative identity for the number of pair partitions, `(2n)!/(2^n n!)`.

This is a formal bridge: the paper-backed mathematical estimate is the
pairing-count version imported below, and the second imported child evaluates
the number of pairings. -/
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  rw [← buchholz_pairing_count_eq_factorial_ratio n]
  exact
    buchholz_matched_walk_sum_le_pairing_count_row_column_energy_moments
      n hn Omega p hp X
