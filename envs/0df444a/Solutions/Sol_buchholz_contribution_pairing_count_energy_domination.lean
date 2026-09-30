-- Prove2me | solution 1 for buchholz_contribution_pairing_count_energy_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-26T14:54:12.685055+00:00
-- url     : https://prove2.me/submissions/29f2a1b6-0ec4-441c-850f-28c1313c257f

import Theorems.Thm_buchholz_contribution_pairing_count_energy_domination_row_case
import Theorems.Thm_buchholz_contribution_pairing_count_energy_domination_column_case

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; Candes--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

This reduction separates the final `max` in the Buchholz contribution bound
from the two substantive energy estimates.  The imported row-case child handles
the branch where the row diagonal energy moment dominates; the imported
column-case child handles the branch where the column diagonal energy moment
dominates.  Linear order trichotomy on real numbers then closes the original
pairing-count bound.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    Finset.univ.sum (fun rows : Fin n → Fin n1 =>
      Finset.univ.sum (fun cols : Fin n → Fin n2 =>
        buchholzMatchedWalkContribution Omega p X rows cols))
      ≤ (Fintype.card (BuchholzPairing n) : ℝ) *
          max
            (Finset.univ.sum (fun i : Fin n1 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
            (Finset.univ.sum (fun j : Fin n2 =>
              (p⁻¹ ^ 2 *
                (Finset.univ.sum
                  (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n)) := by
  let rowEnergy : ℝ :=
    Finset.univ.sum (fun i : Fin n1 =>
      (p⁻¹ ^ 2 *
        (Finset.univ.sum
          (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n)
  let colEnergy : ℝ :=
    Finset.univ.sum (fun j : Fin n2 =>
      (p⁻¹ ^ 2 *
        (Finset.univ.sum
          (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n)
  by_cases hcol : rowEnergy ≤ colEnergy
  · exact
      buchholz_contribution_pairing_count_energy_domination_column_case
        n hn Omega p hp X hcol
  · have hrow : colEnergy ≤ rowEnergy := le_of_lt (lt_of_not_ge hcol)
    exact
      buchholz_contribution_pairing_count_energy_domination_row_case
        n hn Omega p hp X hrow
