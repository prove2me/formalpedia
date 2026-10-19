-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalPowerRemainder_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/d58b6b4a-8802-4af1-be1f-de059bcfdcc5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalEquationRemainder_outer_totalDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t s d : ℕ} (hd : 3 ≤ d) (coordinate : Fin s × Fin t) :
    (partitionIncidenceGlobalPowerRemainder t s d coordinate).totalDegree <
      d - 1 := by
  classical
  let q := d - 1
  let k : ℂ := ((t - q : ℕ) : ℂ)
  let lead : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
  let B := (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
  let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun row => partitionIncidenceGlobalEquationRemainder
      t s d coordinate.1 row
  let low : MvPolynomial (Fin s × Fin t) B :=
    ∑ j : Fin (d - 2),
      (-MvPolynomial.X coordinate) ^ (q - (j.val + 1)) *
        MvPolynomial.C (MvPolynomial.X (Sum.inr (coordinate.1, j)))
  have hq : 0 < q := by dsimp [q]; omega
  have hCmul (c : B) (f : MvPolynomial (Fin s × Fin t) B) :
      (MvPolynomial.C c * f).totalDegree ≤ f.totalDegree := by
    calc
      (MvPolynomial.C c * f).totalDegree ≤
          (MvPolynomial.C c).totalDegree + f.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = f.totalDegree := by
        rw [MvPolynomial.totalDegree_C, Nat.zero_add]
  have hR (row : Fin t) :
      (partitionIncidenceGlobalColumnLift t s d (R row)).totalDegree ≤
        q - 1 := by
    dsimp [R, q]
    simpa [Nat.sub_sub] using
      partitionIncidenceGlobalEquationRemainder_outer_totalDegree
        t s d coordinate.1 row
  have hlow : low.totalDegree ≤ q - 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    calc
      ((-MvPolynomial.X coordinate :
          MvPolynomial (Fin s × Fin t) B) ^
            (q - (j.val + 1)) *
          MvPolynomial.C
            (MvPolynomial.X (Sum.inr (coordinate.1, j)))).totalDegree ≤
        ((-MvPolynomial.X coordinate :
          MvPolynomial (Fin s × Fin t) B) ^
            (q - (j.val + 1))).totalDegree +
          (MvPolynomial.C
            (MvPolynomial.X (Sum.inr (coordinate.1, j))) :
              MvPolynomial (Fin s × Fin t) B).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (q - (j.val + 1)) *
          (-MvPolynomial.X coordinate :
            MvPolynomial (Fin s × Fin t) B).totalDegree + 0 := by
        gcongr
        · exact MvPolynomial.totalDegree_pow _ _
        · exact (MvPolynomial.totalDegree_C _).le
      _ ≤ q - 1 := by
        have hj : j.val + 1 ≤ q := by
          have hj' := j.isLt
          dsimp [q]
          omega
        rw [MvPolynomial.totalDegree_neg,
          MvPolynomial.totalDegree_X, Nat.mul_one, Nat.add_zero]
        omega
  have hinside :
      (MvPolynomial.C (MvPolynomial.C (k * lead)) * low +
        MvPolynomial.C (MvPolynomial.C k) *
          partitionIncidenceGlobalColumnLift t s d (R coordinate.2) -
        ∑ row : Fin t,
          partitionIncidenceGlobalColumnLift t s d (R row)).totalDegree ≤
        q - 1 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · exact (hCmul _ low).trans hlow
      · exact (hCmul _ _).trans (hR coordinate.2)
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro row _
      exact hR row
  change
    (MvPolynomial.C (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
      (MvPolynomial.C (MvPolynomial.C (k * lead)) * low +
        MvPolynomial.C (MvPolynomial.C k) *
          partitionIncidenceGlobalColumnLift t s d (R coordinate.2) -
        ∑ row : Fin t,
          partitionIncidenceGlobalColumnLift t s d (R row))).totalDegree < q
  exact lt_of_le_of_lt
    ((hCmul _ _).trans hinside)
    (Nat.sub_lt hq (by omega))
end PermanentRollout
