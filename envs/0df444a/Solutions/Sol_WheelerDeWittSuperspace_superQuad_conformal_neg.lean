-- Prove2me | solution 1 for WheelerDeWittSuperspace.superQuad_conformal_neg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:29:31.830449+00:00
-- url     : https://prove2.me/submissions/42b6a38b-4a6f-4c76-bb00-24c8c7941fe6

import Mathlib
import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

theorem superQuad_trace_form_decdd34a (m p : Matrix (Fin 3) (Fin 3) ℝ) :
    superQuad m p =
      ((pᵀ * m * p * mᵀ).trace + (p * m * p * mᵀ).trace - (p * mᵀ).trace ^ 2) /
        (2 * volume m) := by
  simp only [superQuad, deWitt, Fin.sum_univ_three, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  ring

end WheelerDeWittSuperspace

open Matrix in
open WheelerDeWittSuperspace in
theorem solution (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef) :
    superQuad m m⁻¹ < 0 := by
  have hdet : 0 < m.det := hm.det_pos
  have hu : IsUnit m.det := isUnit_iff_ne_zero.mpr hdet.ne'
  have hT : mᵀ = m := by
    have h1 := hm.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have hnT : (m⁻¹)ᵀ = m⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have hnm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hu
  rw [WheelerDeWittSuperspace.superQuad_trace_form_decdd34a, hnT, hT, hnm, one_mul, hnm]
  have hv : 0 < WheelerDeWittSuperspace.volume m := by
    unfold WheelerDeWittSuperspace.volume; exact Real.sqrt_pos.mpr hdet
  simp only [Matrix.trace_one, Fintype.card_fin]
  apply div_neg_of_neg_of_pos
  · norm_num
  · positivity
