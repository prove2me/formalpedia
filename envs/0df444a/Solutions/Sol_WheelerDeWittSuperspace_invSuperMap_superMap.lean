-- Prove2me | solution 1 for WheelerDeWittSuperspace.invSuperMap_superMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:52:54.86732+00:00
-- url     : https://prove2.me/submissions/5ab9dd1c-69f3-46a1-a400-48b6997597e9

import Mathlib
import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

theorem superMap_eq_44503ea3 (m p : Matrix (Fin 3) (Fin 3) ℝ) :
    superMap m p = (2 * volume m)⁻¹ •
      (m * p * mᵀ + m * pᵀ * mᵀ - (mᵀ * p).trace • m) := by
  ext a b
  simp only [superMap, deWitt, Matrix.of_apply, Fin.sum_univ_three, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, smul_eq_mul]
  ring

theorem invSuperMap_eq_44503ea3 (m k : Matrix (Fin 3) (Fin 3) ℝ) :
    invSuperMap m k = (volume m / 2) •
      (m⁻¹ * k * (m⁻¹)ᵀ + m⁻¹ * kᵀ * (m⁻¹)ᵀ - (2 * ((m⁻¹)ᵀ * k).trace) • m⁻¹) := by
  ext a b
  simp only [invSuperMap, invDeWitt, Matrix.of_apply, Fin.sum_univ_three, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, smul_eq_mul]
  ring

end WheelerDeWittSuperspace

open Matrix WheelerDeWittSuperspace in
theorem solution (m p : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef) (hp : pᵀ = p) :
    invSuperMap m (superMap m p) = p := by
  have hdet : 0 < m.det := hm.det_pos
  have hu : IsUnit m.det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hT : mᵀ = m := by
    have h1 := hm.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have hnT : (m⁻¹)ᵀ = m⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have hnm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hu
  have hmn : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hu
  have hv : 0 < volume m := by
    unfold volume; exact Real.sqrt_pos.mpr hdet
  set V := volume m with hV
  set n := m⁻¹ with hn
  set t := (m * p).trace with ht
  have h1 : n * (m * p * m) * n = p := by
    rw [show n * (m * p * m) * n = (n * m) * p * (m * n) by simp only [Matrix.mul_assoc]]
    rw [hnm, hmn, Matrix.one_mul, Matrix.mul_one]
  have h2 : n * m * n = n := by rw [hnm, Matrix.one_mul]
  have h3 : (n * (m * p * m)).trace = t := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hmn, Matrix.mul_one]
  have h4 : (n * m).trace = 3 := by
    rw [hnm, Matrix.trace_one, Fintype.card_fin]; norm_num
  have hq : superMap m p = (2 * V)⁻¹ • ((2 : ℝ) • (m * p * m) - t • m) := by
    rw [superMap_eq_44503ea3, hT, hp, two_smul]
  have hqT : (superMap m p)ᵀ = superMap m p := by
    rw [hq, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_smul, hT, Matrix.transpose_mul, Matrix.transpose_mul, hT, hp,
      Matrix.mul_assoc]
  rw [invSuperMap_eq_44503ea3, hqT, ← hn, ← hV, hnT]
  rw [hq]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_smul, Matrix.trace_sub, h1, h2, h3, h4, smul_eq_mul]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring
