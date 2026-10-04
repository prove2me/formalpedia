-- Prove2me | solution 1 for PolyakovAction.sqrt_neg_det_variation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:02:57.582748+00:00
-- url     : https://prove2.me/submissions/89266167-af92-4f55-ab1a-5f4247e7a6a0

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

open scoped Matrix Topology in
theorem solution (k δk : Matrix (Fin 2) (Fin 2) ℝ) (hk : k.det < 0)
    (hksymm : kᵀ = k) :
    HasDerivAt (fun t : ℝ => Real.sqrt (-((k + t • δk)⁻¹).det))
      (-(1 / 2) * Real.sqrt (-(k⁻¹).det) * ∑ a, ∑ b, k⁻¹ a b * δk a b) 0 := by
  set p : ℝ → ℝ := fun t => (k 0 0 + t * δk 0 0) * (k 1 1 + t * δk 1 1)
    - (k 0 1 + t * δk 0 1) * (k 1 0 + t * δk 1 0) with hpdef
  have hfun : (fun t : ℝ => Real.sqrt (-((k + t • δk)⁻¹).det))
      = fun t => Real.sqrt (-(p t)⁻¹) := by
    funext t
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_fin_two]
    simp [p, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hp0 : p 0 = k.det := by simp [p, Matrix.det_fin_two]
  have hp : HasDerivAt p
      (δk 0 0 * k 1 1 + k 0 0 * δk 1 1 - (δk 0 1 * k 1 0 + k 0 1 * δk 1 0)) 0 := by
    have e : ∀ i j, HasDerivAt (fun t : ℝ => k i j + t * δk i j) (δk i j) 0 := by
      intro i j
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (δk i j)).const_add (k i j)
    have := ((e 0 0).mul (e 1 1)).sub ((e 0 1).mul (e 1 0))
    simp only [zero_mul, add_zero] at this
    exact this
  have hD : k.det ≠ 0 := hk.ne
  have hpinv := (hp.inv (by rw [hp0]; exact hD)).neg
  have hpos : 0 < -(p 0)⁻¹ := by
    rw [hp0]; exact neg_pos.mpr (inv_lt_zero.mpr hk)
  have hs := hpinv.sqrt hpos.ne'
  rw [hfun]
  convert hs using 1
  · funext t; rfl
  simp only [Pi.neg_apply, Pi.inv_apply, hp0]
  have h10 : k 1 0 = k 0 1 := by
    simpa using congrFun (congrFun hksymm 0) 1
  have a00 : k.adjugate 0 0 = k 1 1 := by simp [Matrix.adjugate_fin_two]
  have a01 : k.adjugate 0 1 = -k 0 1 := by simp [Matrix.adjugate_fin_two]
  have a10 : k.adjugate 1 0 = -k 1 0 := by simp [Matrix.adjugate_fin_two]
  have a11 : k.adjugate 1 1 = k 0 0 := by simp [Matrix.adjugate_fin_two]
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, a00, a01, a10, a11]
  have hu2 : Real.sqrt (-k.det⁻¹) ^ 2 = -k.det⁻¹ :=
    Real.sq_sqrt (neg_nonneg.mpr (inv_nonpos.mpr hk.le))
  have hu : Real.sqrt (-k.det⁻¹) ≠ 0 :=
    (Real.sqrt_pos.mpr (neg_pos.mpr (inv_lt_zero.mpr hk))).ne'
  set D := k.det with hDdef
  set u := Real.sqrt (-D⁻¹) with hudef
  rw [h10]
  have hinv : u⁻¹ = -D * u :=
    (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, ← sq, hu2, neg_mul_neg, mul_inv_cancel₀ hD])).symm
  rw [div_eq_mul_inv _ (2 * u), mul_inv, hinv]
  field_simp
  ring
