-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P11.affine_skein_on_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:16:42.273365+00:00
-- url     : https://prove2.me/submissions/2a8d15bc-5dbe-4d5d-b914-420bae8f1470

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
noncomputable section

open scoped BigOperators Classical

theorem g66h_x2pow {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (x1 x2 e : A)
    (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1) (m : ℕ) :
    x2 * (x1 ^ m * e) = -(x1 ^ (m+1) * e) := by
  have hc : Commute x2 (x1 ^ m) := (Commute.pow_right (h3.symm) m)
  rw [← mul_assoc, hc.eq, mul_assoc, h2, mul_neg, ← mul_assoc, pow_succ]

theorem g66h_skein {S A : Type*} [CommRing S] [Ring A] [Algebra S A] (omega : ℕ → S)
    (x1 x2 s e : A)
    (h1 : s * x1 = x2 * s + e - 1) (h2 : x2 * e = -(x1 * e)) (h3 : x1 * x2 = x2 * x1)
    (h4 : s * e = e) (h5 : ∀ a, e * x1 ^ a * e = omega a • e) :
    ∀ a : ℕ, s * x1 ^ a * e = (-1 : S) ^ a • (x1 ^ a * e) +
      (∑ k ∈ Finset.range a, ((-1 : S) ^ k * omega (a - 1 - k)) • (x1 ^ k * e)) -
      (if Odd a then x1 ^ (a - 1) * e else 0) := by
  intro a
  induction a with
  | zero => simp [h4]
  | succ a ih =>
    have step : s * x1 ^ (a+1) * e = x2 * (s * x1 ^ a * e) + omega a • e - x1 ^ a * e := by
      rw [pow_succ', ← mul_assoc s, h1, ← h5 a]; noncomm_ring
    rw [step, ih, mul_sub, mul_add, mul_smul_comm, g66h_x2pow (S := S) x1 x2 e h2 h3, Finset.mul_sum]
    simp only [mul_smul_comm, g66h_x2pow (S := S) x1 x2 e h2 h3]
    rw [Finset.sum_range_succ' _ a]
    have hs : ∀ k ∈ Finset.range a, ((-1 : S) ^ (k+1) * omega (a + 1 - 1 - (k+1))) • (x1 ^ (k+1) * e)
        = ((-1 : S) ^ k * omega (a - 1 - k)) • -(x1 ^ (k + 1) * e) := by
      intro k hk
      rw [show a + 1 - 1 - (k+1) = a - 1 - k by omega, pow_succ, smul_neg, mul_comm _ (-1 : S),
        mul_assoc, neg_one_mul, neg_smul]
    rw [Finset.sum_congr rfl hs]
    simp only [Nat.add_sub_cancel, pow_zero, one_mul, Nat.sub_zero, Nat.odd_add_one]
    rcases Nat.even_or_odd a with he | ho
    · have hno : ¬ Odd a := Nat.not_odd_iff_even.mpr he
      simp only [hno, if_false, not_false_eq_true, if_true, mul_zero, sub_zero, pow_succ, mul_neg,
        mul_one, neg_smul, smul_neg]
      abel
    · have hno : ¬ ¬ Odd a := not_not.mpr ho
      have ha1 : a - 1 + 1 = a := by obtain ⟨m, rfl⟩ := ho; omega
      simp only [ho, hno, if_true, if_false, not_true_eq_false]
      rw [g66h_x2pow (S := S) x1 x2 e h2 h3 (a-1), ha1]
      simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]
      abel

theorem g66h_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a : ℕ) :
    ∑ b ∈ Finset.Icc 1 a, f b = ∑ k ∈ Finset.range a, f (k + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_aff_rels (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ) (hn : 2 ≤ n) :
    affineS S omega n 0 * affineX S omega n 0 =
        affineX S omega n 1 * affineS S omega n 0 + affineE S omega n 0 - 1 ∧
    affineX S omega n 1 * affineE S omega n 0 = -(affineX S omega n 0 * affineE S omega n 0) ∧
    affineX S omega n 0 * affineX S omega n 1 = affineX S omega n 1 * affineX S omega n 0 ∧
    affineS S omega n 0 * affineE S omega n 0 = affineE S omega n 0 ∧
    affineE S omega n 0 * affineS S omega n 0 = affineE S omega n 0 ∧
    (∀ a, affineE S omega n 0 * affineX S omega n 0 ^ a * affineE S omega n 0 =
      omega a • affineE S omega n 0) := by
  have q : ∀ {x y}, BMWRel S omega n x y → affineBMWQuotientMap S omega n x =
      affineBMWQuotientMap S omega n y := fun h => RingQuot.mkAlgHom_rel S h
  have r1 := q (BMWRel.skeinLeft 0 (by omega))
  have r2 := q (BMWRel.antisymRight 0 (by omega))
  have r3 := q (BMWRel.xxCommute 0 1 (by omega) (by omega))
  have r4 := q (BMWRel.se 0 (by omega))
  have r5 := q (BMWRel.es 0 (by omega))
  have r6 := q (BMWRel.idempotent 0 (by omega))
  have r7 : ∀ a, 0 < a → _ := fun a ha => q (BMWRel.unwrap a ha hn)
  simp only [map_sub, map_mul, map_one, map_add, map_zero, map_pow, AlgHom.commutes] at r1 r2 r3 r4 r5 r6 r7
  refine ⟨?_, ?_, r3, r4, r5, ?_⟩
  · change affineS S omega n 0 * affineX S omega n 0 - affineX S omega n 1 * affineS S omega n 0 =
      affineE S omega n 0 - 1 at r1
    rw [add_sub_assoc, ← r1]; abel
  · change (affineX S omega n 0 + affineX S omega n 1) * affineE S omega n 0 = 0 at r2
    rw [add_mul] at r2
    exact eq_neg_of_add_eq_zero_right r2
  · intro a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [pow_zero, mul_one, ← pow_two, Algebra.smul_def]; exact r6
    · rw [Algebra.smul_def]; exact r7 a ha

open QAlgorithms.Papers.Independent.Renew46.P16 in
theorem g66h_aff_skein (S : Type*) [CommRing S] (omega : ℕ → S)
    (n a : ℕ) (hn : 2 ≤ n) :
    affineS S omega n 0 * affineX S omega n 0 ^ a * affineE S omega n 0 =
      (-1 : S) ^ a • (affineX S omega n 0 ^ a * affineE S omega n 0) +
      (∑ b ∈ Finset.Icc 1 a, ((-1 : S) ^ (b - 1) * omega (a - b)) •
        (affineX S omega n 0 ^ (b - 1) * affineE S omega n 0)) -
      (if Odd a then affineX S omega n 0 ^ (a - 1) * affineE S omega n 0 else 0) := by
  obtain ⟨h1, h2, h3, h4, -, h5⟩ := g66h_aff_rels S omega n hn
  rw [g66h_Icc, g66h_skein omega _ _ _ _ h1 h2 h3 h4 h5 a]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.add_sub_cancel]
  congr 3
  omega

open QAlgorithms.Papers.Independent.Support21.P11 QAlgorithms.Papers.Independent.Renew46.P16 in
theorem solution (R : Type*) [CommRing R] (omega : ℕ → R)
    (n a : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) :
    affineS R omega n 0 * affineX R omega n 0 ^ a * affineE R omega n 0 =
      (-1 : R) ^ a • (affineX R omega n 0 ^ a * affineE R omega n 0) +
      (∑ b ∈ Finset.Icc 1 a, ((-1 : R) ^ (b - 1) * omega (a - b)) •
        (affineX R omega n 0 ^ (b - 1) * affineE R omega n 0)) -
      (if Odd a then affineX R omega n 0 ^ (a - 1) * affineE R omega n 0 else 0) := by
  convert g66h_aff_skein R omega n a hn
