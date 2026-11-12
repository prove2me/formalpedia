-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.skeinPower
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:44:40.373178+00:00
-- url     : https://prove2.me/submissions/906e39d1-24cf-43e1-bbda-d13b44e8b723

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

universe u v

open QAlgorithms.Papers.Independent.Intake100.P65 in
theorem solution (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (n i a : ℕ) (hn : 1 ≤ n)
    (hi : i+1 < n) (ha : 1 ≤ a) :
    affineS R omega n i * affineX R omega n i ^ a =
      affineX R omega n (i+1) ^ a * affineS R omega n i +
        ∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
          (affineE R omega n i - 1) * affineX R omega n i ^ (a-b) := by
  have h := RingQuot.mkAlgHom_rel R
    (QAlgorithms.Papers.Independent.Renew46.P16.BMWRel.skeinLeft (S := R) (omega := omega)
      (n := n) i hi)
  simp only [_root_.map_sub, _root_.map_mul, _root_.map_one] at h
  have hrel0 : affineS R omega n i * affineX R omega n i -
      affineX R omega n (i+1) * affineS R omega n i = affineE R omega n i - 1 := h
  have hrel : affineS R omega n i * affineX R omega n i =
      affineX R omega n (i+1) * affineS R omega n i + (affineE R omega n i - 1) := by
    rw [← hrel0]
    abel
  clear ha
  induction a with
  | zero =>
    rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by norm_num)]
    simp
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ a + 1 by omega)]
    have hsum : (∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
          (affineE R omega n i - 1) * affineX R omega n i ^ (a-b)) * affineX R omega n i =
        ∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
          (affineE R omega n i - 1) * affineX R omega n i ^ (a + 1 - b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mem_Icc] at hb
      rw [show a + 1 - b = a - b + 1 by omega, pow_succ]
      simp only [mul_assoc]
    have hYpow : affineX R omega n (i+1) ^ a * (affineX R omega n (i+1) * affineS R omega n i) =
        affineX R omega n (i+1) ^ (a+1) * affineS R omega n i := by
      rw [← mul_assoc, ← pow_succ]
    have hlast : affineX R omega n (i+1) ^ (a + 1 - 1) * (affineE R omega n i - 1) *
        affineX R omega n i ^ (a + 1 - (a + 1)) =
        affineX R omega n (i+1) ^ a * (affineE R omega n i - 1) := by
      rw [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    calc affineS R omega n i * affineX R omega n i ^ (a + 1)
        = (affineS R omega n i * affineX R omega n i ^ a) * affineX R omega n i := by
          rw [pow_succ, mul_assoc]
      _ = (affineX R omega n (i+1) ^ a * affineS R omega n i +
            ∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
              (affineE R omega n i - 1) * affineX R omega n i ^ (a-b)) *
            affineX R omega n i := by rw [ih]
      _ = affineX R omega n (i+1) ^ a * (affineS R omega n i * affineX R omega n i) +
            (∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
              (affineE R omega n i - 1) * affineX R omega n i ^ (a-b)) *
            affineX R omega n i := by rw [add_mul, mul_assoc]
      _ = affineX R omega n (i+1) ^ a *
            (affineX R omega n (i+1) * affineS R omega n i + (affineE R omega n i - 1)) +
            ∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
              (affineE R omega n i - 1) * affineX R omega n i ^ (a + 1 - b) := by
          rw [hrel, hsum]
      _ = affineX R omega n (i+1) ^ (a + 1) * affineS R omega n i +
            ((∑ b ∈ Finset.Icc 1 a, affineX R omega n (i+1) ^ (b-1) *
              (affineE R omega n i - 1) * affineX R omega n i ^ (a + 1 - b)) +
              affineX R omega n (i+1) ^ (a + 1 - 1) * (affineE R omega n i - 1) *
                affineX R omega n i ^ (a + 1 - (a + 1))) := by
          rw [hlast, mul_add, hYpow]
          abel

end
