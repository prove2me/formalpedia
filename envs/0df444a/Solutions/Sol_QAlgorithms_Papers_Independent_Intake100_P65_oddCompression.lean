-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.oddCompression
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T15:14:47.156228+00:00
-- url     : https://prove2.me/submissions/1dc155af-43ab-49af-8cae-93e90660d501

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v


theorem AuxOC_core {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (E S X Y : A) (w : ℕ → R)
    (hEE : E * E = w 0 • E) (hEXE : ∀ m, 0 < m → E * X^m * E = w m • E)
    (hXY : X * Y = Y * X) (hEY : E * Y = -(E * X)) (hsk : S * X - Y * S = E - 1)
    (hES : E * S = E) (hSE : S * E = E) (k : ℕ) :
    (w k - (-1 : R)^k * w k) • E =
      (∑ j ∈ Finset.range k, ((-1 : R)^j * w j * w (k-1-j) - (-1 : R)^j * w (k-1))) • E := by
  have hEXm : ∀ m, E * X^m * E = w m • E := by
    intro m; rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hEE
    · exact hEXE m hm
  have hEYj : ∀ j, E * Y^j = (-1 : R)^j • (E * X^j) := by
    intro j; induction j with
    | zero => simp
    | succ j ih =>
      have hc : X^j * Y = Y * X^j := ((Commute.pow_left hXY j)).eq
      rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hc, ← mul_assoc, hEY, pow_succ,
        pow_succ]
      simp [mul_assoc, smul_neg, neg_smul]
      rw [(Commute.self_pow X j).eq]
  have tele : ∀ k, S * X^k - Y^k * S =
      ∑ j ∈ Finset.range k, Y^j * (E - 1) * X^(k-1-j) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have e : S * X^(k+1) - Y^(k+1) * S = (S * X^k - Y^k * S) * X + Y^k * (S * X - Y * S) := by
        rw [pow_succ, pow_succ]; noncomm_ring
      rw [e, ih, hsk, Finset.sum_range_succ, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        rw [mul_assoc, ← pow_succ, show k-1-j+1 = k+1-1-j by omega]
      · simp
  have lhs : E * (S * X^k - Y^k * S) * E = (w k - (-1 : R)^k * w k) • E := by
    rw [mul_sub, sub_mul, ← mul_assoc E S, hES, show E * (Y^k * S) * E = E * Y^k * (S * E) by
      noncomm_ring, hSE, hEYj, smul_mul_assoc, hEXm, smul_smul, sub_smul]
  rw [← lhs, tele, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e1 : E * (Y^j * (E - 1) * X^(k-1-j)) * E =
      E * Y^j * E * X^(k-1-j) * E - E * Y^j * X^(k-1-j) * E := by noncomm_ring
  have a1 : E * Y^j * E * X^(k-1-j) * E = ((-1 : R)^j * w j * w (k-1-j)) • E := by
    simp only [hEYj, smul_mul_assoc, hEXm, smul_smul]
  have a2 : E * Y^j * X^(k-1-j) * E = ((-1 : R)^j * w (k-1)) • E := by
    simp only [hEYj, smul_mul_assoc]
    rw [mul_assoc E, ← pow_add, show j + (k-1-j) = k-1 by omega, hEXm, smul_smul]
  rw [e1, a1, a2, ← sub_smul]

theorem AuxOC_alt {R : Type*} [CommRing R] (a : ℕ) :
    ∑ j ∈ Finset.range (2*a+1), (-1 : R)^j = 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show 2*(a+1)+1 = 2*a+1+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      pow_succ, pow_succ, pow_mul]
    simp [pow_succ, pow_mul]

theorem oddCompression (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) :
    omega (2*a+1) • affineE R omega n 0 =
      (⅟ (2 : R) * (-omega (2*a) +
        ∑ b ∈ Finset.range (2*a+1), (-1 : R)^b * omega b * omega (2*a-b))) •
          affineE R omega n 0 := by
  have hq : ∀ {x y}, BMWRel R omega n x y →
      affineBMWQuotientMap R omega n x = affineBMWQuotientMap R omega n y :=
    fun h => RingQuot.mkAlgHom_rel R h
  have hEE : affineE R omega n 0 * affineE R omega n 0 = omega 0 • affineE R omega n 0 := by
    have := hq (BMWRel.idempotent 0 (by omega))
    simp only [map_mul, sq, ← Algebra.smul_def, map_smul] at this
    exact this
  have hEXE : ∀ m, 0 < m → affineE R omega n 0 * affineX R omega n 0 ^ m * affineE R omega n 0 =
      omega m • affineE R omega n 0 := by
    intro m hm
    have := hq (BMWRel.unwrap m hm hn)
    simp only [map_mul, map_pow, ← Algebra.smul_def, map_smul] at this
    exact this
  have hXY : affineX R omega n 0 * affineX R omega n 1 = affineX R omega n 1 * affineX R omega n 0 := by
    have := hq (BMWRel.xxCommute 0 1 (by omega) (by omega))
    simp only [map_mul] at this
    exact this
  have hEY : affineE R omega n 0 * affineX R omega n 1 = -(affineE R omega n 0 * affineX R omega n 0) := by
    have := hq (BMWRel.antisymLeft 0 (by omega))
    simp only [map_mul, map_add, map_zero, zero_add] at this
    rw [eq_neg_iff_add_eq_zero, add_comm, ← mul_add]
    exact this
  have hsk : affineS R omega n 0 * affineX R omega n 0 - affineX R omega n 1 * affineS R omega n 0 =
      affineE R omega n 0 - 1 := by
    have := hq (BMWRel.skeinLeft 0 (by omega))
    simp only [map_mul, map_sub, map_one, zero_add] at this
    exact this
  have hES : affineE R omega n 0 * affineS R omega n 0 = affineE R omega n 0 := by
    have := hq (BMWRel.es 0 (by omega))
    simp only [map_mul] at this
    exact this
  have hSE : affineS R omega n 0 * affineE R omega n 0 = affineE R omega n 0 := by
    have := hq (BMWRel.se 0 (by omega))
    simp only [map_mul] at this
    exact this
  have core := AuxOC_core _ _ _ _ omega hEE hEXE hXY hEY hsk hES hSE (2*a+1)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, AuxOC_alt, one_mul] at core
  have e1 : (-1 : R)^(2*a+1) = -1 := by rw [pow_succ, pow_mul]; simp
  rw [e1, show 2*a+1-1 = 2*a by omega] at core
  have h2 : (2 : R) * ⅟ 2 = 1 := by simp
  calc omega (2*a+1) • affineE R omega n 0
      = (⅟ (2 : R) * (omega (2*a+1) - -1 * omega (2*a+1))) • affineE R omega n 0 := by
        congr 1; linear_combination (-omega (2*a+1)) * h2
    _ = _ := by
        rw [mul_smul, core, ← mul_smul]
        congr 1
        ring

end QAlgorithms.Papers.Independent.Intake100.P65

end

theorem solution (R : Type*) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n : ℕ) (hn : 2 ≤ n) (a : ℕ) :
    omega (2*a+1) • QAlgorithms.Papers.Independent.Renew46.P16.affineE R omega n 0 =
      (⅟ (2 : R) * (-omega (2*a) +
        ∑ b ∈ Finset.range (2*a+1), (-1 : R)^b * omega b * omega (2*a-b))) •
          QAlgorithms.Papers.Independent.Renew46.P16.affineE R omega n 0 :=
  QAlgorithms.Papers.Independent.Intake100.P65.oddCompression R omega n hn a
