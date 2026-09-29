-- Prove2me | solution 1 for buchholz_contribution_pairing_count_energy_domination_column_case
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-26T15:29:58.155174+00:00
-- url     : https://prove2.me/submissions/a45cdfaf-d60c-48e8-997d-c07ae94b4e97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_buchholz_contribution_pairing_count_column_energy_bound

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; Candes--Recht, Section 6.1,
Lemma 6.1, PDF p. 25.

This is a formal wrapper around the column-dominant Buchholz energy estimate.
The imported child gives the bound with the column energy on the right-hand
side.  The hypothesis of this target says the column energy is at least the row
energy, so the `max` in the target is exactly the column energy.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2)
    (hcol :
      (Finset.univ.sum (fun i : Fin n1 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))
        ≤
      (Finset.univ.sum (fun j : Fin n2 =>
        (p⁻¹ ^ 2 *
          (Finset.univ.sum
            (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0))) ^ n))) :
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
  rw [max_eq_right hcol]
  exact buchholz_contribution_pairing_count_column_energy_bound n hn Omega p hp X hcol
