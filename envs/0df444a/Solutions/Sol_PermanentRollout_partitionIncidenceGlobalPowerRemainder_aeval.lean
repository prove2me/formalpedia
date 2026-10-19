-- Prove2me | solution 1 for PermanentRollout.partitionIncidenceGlobalPowerRemainder_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/61133d74-745e-46f2-b670-9dfbf4941285

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionIncidence_monicReduction_mem
import Theorems.Thm_PermanentRollout_partitionIncidenceGlobalColumnLift_aeval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t)
    (coordinate : Fin s × Fin t) :
    letI := partitionIncidenceGlobalBaseAlgebra t s d
    (Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
      (MvPolynomial.X (Sum.inr coordinate))) ^ (d - 1) =
      MvPolynomial.aeval
        (fun row : Fin s × Fin t =>
          Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.X (Sum.inr row)))
        (partitionIncidenceGlobalPowerRemainder t s d coordinate) := by
  classical
  letI := partitionIncidenceGlobalBaseAlgebra t s d
  let q := d - 1
  let k : ℂ := ((t - q : ℕ) : ℂ)
  let a : ℂ := (-1 : ℂ) ^ q * (q.factorial : ℂ)
  let I := partitionIncidenceIdeal t s d
  let x : Fin s × Fin t → PartitionIncidenceCoordinateRing t s d :=
    fun row => Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr row))
  let embed : Fin t → IncidenceCoordinate t s :=
    fun row => Sum.inr (coordinate.1, row)
  let E : ℕ → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun j => MvPolynomial.rename embed
      (partitionFiberCoordinateEsymmPolynomial t j)
  let R : Fin t → MvPolynomial (IncidenceCoordinate t s) ℂ :=
    fun row => partitionIncidenceEquation t s d coordinate.1 row -
      MvPolynomial.C a * MvPolynomial.rename embed
        (deletedCoordinateEsymmPolynomial t q row)
  let low : MvPolynomial (Fin s × Fin t)
      (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ) :=
    ∑ j : Fin (d - 2),
      (-MvPolynomial.X coordinate) ^ (q - (j.val + 1)) *
        MvPolynomial.C (MvPolynomial.X (Sum.inr (coordinate.1, j)))
  have hlift (f : MvPolynomial (IncidenceCoordinate t s) ℂ) :
      MvPolynomial.aeval x (partitionIncidenceGlobalColumnLift t s d f) =
        Ideal.Quotient.mk I f :=
    partitionIncidenceGlobalColumnLift_aeval t s d f
  have hcertificate :
      MvPolynomial.C k *
        (MvPolynomial.C a *
          (∑ j ∈ Finset.range q,
            (-MvPolynomial.X (Sum.inr coordinate)) ^ (q - j) * E j) +
            R coordinate.2) -
          ∑ row : Fin t, R row ∈ I := by
    simpa [q, k, a, I, embed, E, R] using
      partitionIncidence_monicReduction_mem t s d coordinate.1 coordinate.2
  have hzero : Ideal.Quotient.mk I
      (MvPolynomial.C k *
        (MvPolynomial.C a *
          (∑ j ∈ Finset.range q,
            (-MvPolynomial.X (Sum.inr coordinate)) ^ (q - j) * E j) +
            R coordinate.2) -
          ∑ row : Fin t, R row) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hcertificate
  have hk : k ≠ 0 := by
    dsimp [k, q]
    exact_mod_cast (show t - (d - 1) ≠ 0 by omega)
  have hfact : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero q
  have hbase (j : Fin (d - 2)) :
      algebraMap
        (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
        (PartitionIncidenceCoordinateRing t s d)
        (MvPolynomial.X (Sum.inr (coordinate.1, j))) =
        Ideal.Quotient.mk I (E (j.val + 1)) := by
    change partitionIncidenceGlobalBaseProjection t s d
      (MvPolynomial.X (Sum.inr (coordinate.1, j))) = _
    simp [partitionIncidenceGlobalBaseProjection, E, embed, I]
  have hconst (c : ℂ) :
      algebraMap
        (MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)
        (PartitionIncidenceCoordinateRing t s d) (MvPolynomial.C c) =
        Ideal.Quotient.mk I (MvPolynomial.C c) := by
    change partitionIncidenceGlobalBaseProjection t s d
      (MvPolynomial.C c) = _
    simpa [partitionIncidenceGlobalBaseProjection, I] using
      (Ideal.Quotient.mk_algebraMap (R₁ := ℂ) I c).symm
  have hloweval :
      MvPolynomial.aeval x low =
        ∑ j : Fin (d - 2),
          (-x coordinate) ^ (q - (j.val + 1)) *
            Ideal.Quotient.mk I (E (j.val + 1)) := by
    dsimp [low]
    simp only [map_sum, map_mul, map_pow, map_neg,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp_rw [hbase]
  have hsplitSource :
      (∑ j ∈ Finset.range q,
        (-MvPolynomial.X coordinate.2) ^ (q - j) *
          partitionFiberCoordinateEsymmPolynomial t j) =
        (-MvPolynomial.X coordinate.2 : MvPolynomial (Fin t) ℂ) ^ q +
        ∑ j : Fin (d - 2),
          (-MvPolynomial.X coordinate.2) ^ (q - (j.val + 1)) *
            partitionFiberCoordinateEsymmPolynomial t (j.val + 1) := by
    have hqeq : q = (d - 2) + 1 := by dsimp [q]; omega
    conv_lhs => rw [hqeq, Finset.sum_range_succ']
    simp only [Nat.sub_zero, partitionFiberCoordinateEsymmPolynomial,
      MvPolynomial.esymm_zero, mul_one]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ =>
        (-MvPolynomial.X coordinate.2 : MvPolynomial (Fin t) ℂ) ^
          (q - (j + 1)) * MvPolynomial.esymm (Fin t) ℂ (j + 1))
      (d - 2)]
    simp [hqeq, add_comm]
  have hsplit :
      (∑ j ∈ Finset.range q,
        (-MvPolynomial.X (Sum.inr coordinate)) ^ (q - j) * E j) =
        (-MvPolynomial.X (Sum.inr coordinate) :
          MvPolynomial (IncidenceCoordinate t s) ℂ) ^ q +
        ∑ j : Fin (d - 2),
          (-MvPolynomial.X (Sum.inr coordinate)) ^ (q - (j.val + 1)) *
            E (j.val + 1) := by
    have h := congrArg (MvPolynomial.rename embed) hsplitSource
    simpa [E, embed, map_sum, map_add, map_mul, map_pow, map_neg]
      using h
  change x coordinate ^ q =
    MvPolynomial.aeval x (partitionIncidenceGlobalPowerRemainder t s d coordinate)
  unfold partitionIncidenceGlobalPowerRemainder
  change x coordinate ^ q =
    MvPolynomial.aeval x
      (MvPolynomial.C (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
        (MvPolynomial.C (MvPolynomial.C (k * a)) * low +
          MvPolynomial.C (MvPolynomial.C k) *
            partitionIncidenceGlobalColumnLift t s d (R coordinate.2) -
          ∑ row : Fin t, partitionIncidenceGlobalColumnLift t s d (R row)))
  simp only [map_mul, map_add, map_sub, map_sum, MvPolynomial.aeval_C]
  simp_rw [hconst, hlift]
  rw [hloweval]
  rw [hsplit] at hzero
  simp only [map_sub, map_mul, map_add, map_sum, map_pow, map_neg] at hzero
  have hsign : a * (-1 : ℂ) ^ q = (q.factorial : ℂ) := by
    have heven : Even (q + q) := ⟨q, by omega⟩
    calc
      a * (-1 : ℂ) ^ q =
          ((-1 : ℂ) ^ q * (-1 : ℂ) ^ q) * (q.factorial : ℂ) := by
        dsimp [a]
        ring
      _ = (-1 : ℂ) ^ (q + q) * (q.factorial : ℂ) := by rw [pow_add]
      _ = (q.factorial : ℂ) := by rw [heven.neg_one_pow]; ring
  have hunit : k * (q.factorial : ℂ) ≠ 0 := mul_ne_zero hk hfact
  have hsign_quot :
      Ideal.Quotient.mk I (MvPolynomial.C a) * (-x coordinate) ^ q =
        Ideal.Quotient.mk I (MvPolynomial.C (q.factorial : ℂ)) *
          x coordinate ^ q := by
    rw [← neg_one_mul (x coordinate), mul_pow]
    have hminus :
        (-1 : PartitionIncidenceCoordinateRing t s d) ^ q =
          Ideal.Quotient.mk I (MvPolynomial.C ((-1 : ℂ) ^ q)) := by
      simp
    rw [hminus]
    change Ideal.Quotient.mk I (MvPolynomial.C a) *
        (Ideal.Quotient.mk I (MvPolynomial.C ((-1 : ℂ) ^ q)) *
          x coordinate ^ q) = _
    rw [← mul_assoc, ← map_mul, ← MvPolynomial.C_mul, hsign]
  let S : PartitionIncidenceCoordinateRing t s d :=
    ∑ j : Fin (d - 2),
      (-x coordinate) ^ (q - (j.val + 1)) *
        Ideal.Quotient.mk I (E (j.val + 1))
  let T : PartitionIncidenceCoordinateRing t s d :=
    Ideal.Quotient.mk I (MvPolynomial.C (k * a)) * S +
      Ideal.Quotient.mk I (MvPolynomial.C k) *
        Ideal.Quotient.mk I (R coordinate.2) -
      ∑ row : Fin t, Ideal.Quotient.mk I (R row)
  have hlinear :
      Ideal.Quotient.mk I (MvPolynomial.C (k * (q.factorial : ℂ))) *
        x coordinate ^ q + T = 0 := by
    calc
      _ = Ideal.Quotient.mk I (MvPolynomial.C k) *
          (Ideal.Quotient.mk I (MvPolynomial.C a) *
            ((-x coordinate) ^ q + S) +
            Ideal.Quotient.mk I (R coordinate.2)) -
          ∑ row : Fin t, Ideal.Quotient.mk I (R row) := by
        dsimp [T]
        simp only [map_mul]
        linear_combination
          -(Ideal.Quotient.mk I (MvPolynomial.C k)) * hsign_quot
      _ = 0 := by
        simpa [S, x, embed, E] using hzero
  have hinv :
      Ideal.Quotient.mk I
          (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
        Ideal.Quotient.mk I
          (MvPolynomial.C (k * (q.factorial : ℂ))) = -1 := by
    rw [← map_mul, ← MvPolynomial.C_mul, neg_mul,
      inv_mul_cancel₀ hunit]
    simp
  change x coordinate ^ q =
    Ideal.Quotient.mk I
      (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
      (Ideal.Quotient.mk I (MvPolynomial.C k) *
          Ideal.Quotient.mk I (MvPolynomial.C a) * S +
        Ideal.Quotient.mk I (MvPolynomial.C k) *
          Ideal.Quotient.mk I (R coordinate.2) -
        ∑ row : Fin t, Ideal.Quotient.mk I (R row))
  rw [← map_mul, ← MvPolynomial.C_mul]
  change x coordinate ^ q =
    Ideal.Quotient.mk I
      (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) * T
  calc
    x coordinate ^ q =
        -(Ideal.Quotient.mk I
          (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) *
          Ideal.Quotient.mk I
            (MvPolynomial.C (k * (q.factorial : ℂ)))) *
          x coordinate ^ q := by rw [hinv]; ring
    _ = Ideal.Quotient.mk I
          (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) * T := by
      have hscaled := congrArg
        (fun z : PartitionIncidenceCoordinateRing t s d =>
          Ideal.Quotient.mk I
            (MvPolynomial.C (-(k * (q.factorial : ℂ))⁻¹)) * z)
        hlinear
      simp only [mul_zero] at hscaled
      linear_combination -hscaled
end PermanentRollout
