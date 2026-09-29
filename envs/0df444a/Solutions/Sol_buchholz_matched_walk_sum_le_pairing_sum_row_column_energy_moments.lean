-- Prove2me | solution 1 for buchholz_matched_walk_sum_le_pairing_sum_row_column_energy_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-22T15:14:05.14566+00:00
-- url     : https://prove2.me/submissions/cc4267af-04f9-4de3-a1bf-3001458efd25

import Theorems.Thm_buchholz_contribution_pairing_energy_domination

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; Candes--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

This reduction is a formal bridge from the historical `buchholzMatchedWalkSum`
definition to the more explicit one-walk contribution form used in the child.
The analytic/combinatorial content remains in the imported child theorem: it is
the Buchholz charge of the matched closed-walk contributions to pair partitions
and then to the larger row/column diagonal energy moment.  The proof below only
unfolds the two local definitions and preserves the exact bound.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ Finset.univ.sum (fun _pairing : BuchholzPairing n =>
          max
            (Finset.univ.sum (fun i : Fin n1 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
            (Finset.univ.sum (fun j : Fin n2 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))) := by
  simpa [buchholzMatchedWalkSum, buchholzMatchedWalkContribution] using
    buchholz_contribution_pairing_energy_domination n hn Omega p hp X
