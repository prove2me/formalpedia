-- Prove2me | solution 1 for buchholz_matched_walk_contribution_sum_le_pairing_sum_row_column_energy_moments
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-26T17:31:45.448604+00:00
-- url     : https://prove2.me/submissions/bf115602-2155-4fb1-99ca-c76008a73620
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_buchholz_contribution_pairing_count_row_energy_bound
import Theorems.Thm_buchholz_contribution_pairing_count_column_energy_bound

open MatrixCompletion
open scoped BigOperators

/-!
Source: Buchholz, "Operator Khintchine inequality in non-commutative
probability", Math. Ann. 319 (2001), Sections 2--3; used in Candes--Recht,
Section 6.1, Lemma 6.1, PDF p. 25.

This reduction is the final formal assembly of the contribution-level Buchholz
charging estimate.  The two imported children are the substantive row-dominant
and column-dominant energy estimates.  Since the row and column energy moments
are real numbers, one of them is at most the other; in that branch the
corresponding child bounds the contribution sum by the pairing count times the
larger energy.  The remaining step is the finite-sum identity saying that a
constant summed over all Buchholz pairings is its value multiplied by the
number of pairings.
-/

theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    (∑ rows : Fin n → Fin n1,
      ∑ cols : Fin n → Fin n2,
        buchholzMatchedWalkContribution Omega p X rows cols)
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
  · have hbound :
        (∑ rows : Fin n → Fin n1,
          ∑ cols : Fin n → Fin n2,
            buchholzMatchedWalkContribution Omega p X rows cols)
          ≤ (Fintype.card (BuchholzPairing n) : ℝ) * colEnergy := by
      simpa [rowEnergy, colEnergy] using
        buchholz_contribution_pairing_count_column_energy_bound
          n hn Omega p hp X hcol
    have hsum :
        Finset.univ.sum (fun _pairing : BuchholzPairing n =>
            max rowEnergy colEnergy)
          = (Fintype.card (BuchholzPairing n) : ℝ) * colEnergy := by
      simp [max_eq_right hcol]
    exact hbound.trans (le_of_eq hsum.symm)
  · have hrow : colEnergy ≤ rowEnergy := le_of_lt (lt_of_not_ge hcol)
    have hbound :
        (∑ rows : Fin n → Fin n1,
          ∑ cols : Fin n → Fin n2,
            buchholzMatchedWalkContribution Omega p X rows cols)
          ≤ (Fintype.card (BuchholzPairing n) : ℝ) * rowEnergy := by
      simpa [rowEnergy, colEnergy] using
        buchholz_contribution_pairing_count_row_energy_bound
          n hn Omega p hp X hrow
    have hsum :
        Finset.univ.sum (fun _pairing : BuchholzPairing n =>
            max rowEnergy colEnergy)
          = (Fintype.card (BuchholzPairing n) : ℝ) * rowEnergy := by
      simp [max_eq_left hrow]
    exact hbound.trans (le_of_eq hsum.symm)
