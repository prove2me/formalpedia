-- Prove2me | solution 1 for WheelerDeWittSuperspace.velocityQuad_cone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:44:08.152986+00:00
-- url     : https://prove2.me/submissions/7cf6e90c-a8a1-4b31-82c9-1bf7a7fc4e3d

import Mathlib
import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

open WheelerDeWittSuperspace in
theorem solution (mh dh : Matrix (Fin 3) (Fin 3) ℝ) (hmh : mh.PosDef)
    (hdet : mh.det = 1) (htr : (mh⁻¹ * dh).trace = 0) (s ds : ℝ) (hs : 0 < s) :
    velocityQuad (s • mh) (ds • mh + s • dh) =
      -((3 / 4) * Real.sqrt (32 / 3) * s ^ (-(1 / 4 : ℝ)) * ds) ^ 2 +
        (3 / 32) * (Real.sqrt (32 / 3) * s ^ (3 / 4 : ℝ)) ^ 2 *
          ((mh⁻¹ * dh) * (mh⁻¹ * dh)).trace := by
  have hs0 : s ≠ 0 := hs.ne'
  have hu : IsUnit mh.det := by rw [hdet]; exact isUnit_one
  have hmm : mh⁻¹ * mh = 1 := Matrix.nonsing_inv_mul mh hu
  have hinv : (s • mh)⁻¹ = s⁻¹ • mh⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, hmm, inv_mul_cancel₀ hs0, one_smul]
  set A := mh⁻¹ * dh with hA
  set a := ds / s with ha
  have hM : (s • mh)⁻¹ * (ds • mh + s • dh) = a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A := by
    rw [hinv, mul_add, smul_mul_smul_comm, smul_mul_smul_comm, hmm, inv_mul_cancel₀ hs0,
      one_smul, ha, div_eq_inv_mul]
  have hassoc : (s • mh)⁻¹ * (ds • mh + s • dh) * (s • mh)⁻¹ * (ds • mh + s • dh)
      = ((s • mh)⁻¹ * (ds • mh + s • dh)) * ((s • mh)⁻¹ * (ds • mh + s • dh)) := by
    simp only [Matrix.mul_assoc]
  set T := (A * A).trace with hT
  have htr1 : ((a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A) * (a • 1 + A)).trace
      = 3 * a ^ 2 + T := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      smul_mul, mul_smul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htr,
      Fintype.card_fin, smul_eq_mul, hT]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, htr]
    push_cast; simp; ring
  have htr2 : (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + A).trace = 3 * a := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, htr]; simp; ring
  have hvol : volume (s • mh) = (s ^ (1 / 4 : ℝ)) ^ 6 := by
    unfold volume
    rw [Matrix.det_smul, hdet, Fintype.card_fin, mul_one]
    have h4 : s = (s ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
    have hpos : 0 ≤ (s ^ (1 / 4 : ℝ)) ^ 6 := by positivity
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hpos]
    conv_lhs => rw [h4]
    ring
  unfold velocityQuad
  rw [hassoc, hM, htr1, htr2, hvol]
  set t := s ^ (1 / 4 : ℝ) with ht
  have tpos : 0 < t := Real.rpow_pos_of_pos hs _
  have h4 : s = t ^ 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hneg : s ^ (-(1 / 4 : ℝ)) = t⁻¹ := by rw [Real.rpow_neg hs.le]
  have h34 : s ^ (3 / 4 : ℝ) = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hsq : Real.sqrt (32 / 3) ^ 2 = 32 / 3 := Real.sq_sqrt (by norm_num)
  rw [hneg, h34, ha, h4]
  have tne : t ≠ 0 := tpos.ne'
  field_simp
  rw [hsq]
  ring
