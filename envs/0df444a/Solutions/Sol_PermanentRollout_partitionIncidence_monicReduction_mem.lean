-- Prove2me | solution 1 for PermanentRollout.partitionIncidence_monicReduction_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/4998f31c-6a85-4261-8fea-b70c9fdb8be6

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sum_deletedCoordinateEsymmPolynomial
import Theorems.Thm_PermanentRollout_deletedCoordinateEsymmPolynomial_eq_alternating

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t s d : ℕ) (column : Fin s) (i : Fin t) :
    let q := d - 1
    let k : ℂ := ((t - q : ℕ) : ℂ)
    let a : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
    let embed : Fin t → IncidenceCoordinate t s :=
      fun row => Sum.inr (column, row)
    let D : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun row => MvPolynomial.rename embed
        (deletedCoordinateEsymmPolynomial t q row)
    let E : ℕ → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun j => MvPolynomial.rename embed
        (partitionFiberCoordinateEsymmPolynomial t j)
    let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
      fun row => partitionIncidenceEquation t s d column row -
        MvPolynomial.C a * D row
    MvPolynomial.C k *
        (MvPolynomial.C a *
          (∑ j ∈ Finset.range q,
            (-MvPolynomial.X (Sum.inr (column, i))) ^ (q - j) * E j) +
          R i) -
        ∑ row : Fin t, R row ∈ partitionIncidenceIdeal t s d := by
  classical
  dsimp
  let q := d - 1
  let k : ℂ := ((t - q : ℕ) : ℂ)
  let a : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
  let embed : Fin t → IncidenceCoordinate t s :=
    fun row => Sum.inr (column, row)
  let Q : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun row => partitionIncidenceEquation t s d column row
  let D : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun row => MvPolynomial.rename embed
      (deletedCoordinateEsymmPolynomial t q row)
  let E : ℕ → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun j => MvPolynomial.rename embed
      (partitionFiberCoordinateEsymmPolynomial t j)
  let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun row => Q row - MvPolynomial.C a * D row
  have hsource (row : Fin t) :
      Q row = MvPolynomial.C a * D row + R row := by
    dsimp [R]
    ring
  have hsumD :
      (∑ row : Fin t, D row) = MvPolynomial.C k * E q := by
    have h := congrArg
      (MvPolynomial.rename embed)
      (sum_deletedCoordinateEsymmPolynomial t q)
    simpa [D, E, k, map_sum, map_mul] using h
  have hdeleted :
      D i =
        (∑ j ∈ Finset.range q,
          (-MvPolynomial.X (Sum.inr (column, i))) ^ (q - j) * E j) +
        E q := by
    have h := congrArg
      (MvPolynomial.rename embed)
      (deletedCoordinateEsymmPolynomial_eq_alternating t i q)
    rw [Finset.sum_range_succ] at h
    simpa [D, E, embed, map_add, map_sum, map_mul, map_pow, map_neg]
      using h
  have hsumQ :
      (∑ row : Fin t, Q row) =
        MvPolynomial.C a * MvPolynomial.C k * E q +
          ∑ row : Fin t, R row := by
    simp_rw [hsource]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumD]
    ring
  change
    MvPolynomial.C k *
        (MvPolynomial.C a *
          (∑ j ∈ Finset.range q,
            (-MvPolynomial.X (Sum.inr (column, i))) ^ (q - j) * E j) +
          R i) -
        ∑ row : Fin t, R row ∈ partitionIncidenceIdeal t s d
  have heq :
      MvPolynomial.C k *
          (MvPolynomial.C a *
            (∑ j ∈ Finset.range q,
              (-MvPolynomial.X (Sum.inr (column, i))) ^ (q - j) * E j) +
            R i) -
          ∑ row : Fin t, R row =
        MvPolynomial.C k * Q i - ∑ row : Fin t, Q row := by
    rw [hsource i, hdeleted, hsumQ]
    ring
  rw [heq]
  apply Ideal.sub_mem
  · apply Ideal.mul_mem_left
    apply Ideal.subset_span
    exact ⟨(column, i), rfl⟩
  · apply Ideal.sum_mem
    intro row _
    apply Ideal.subset_span
    exact ⟨(column, row), rfl⟩
end PermanentRollout
