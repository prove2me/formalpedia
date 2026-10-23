-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.canonicalComplement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:18:11.588091+00:00
-- url     : https://prove2.me/submissions/650f7e8b-540b-48d9-8ad5-b747245272eb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section
open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap20.P19 in
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel) in
open QAlgorithms.Papers.Independent.Claimed50.P48 (indexedKrausDilation) in
theorem solution (u v : ℝ) :
    QAlgorithms.IsKrausFamily (canonicalKraus u v) ∧
    complementaryChannel (indexedKrausDilation (canonicalKraus u v)) =
      rankTwoQubitMap (v-Real.pi/2) (u-Real.pi/2) := by
  have hK' : canonicalKraus (v - Real.pi / 2) (u - Real.pi / 2) =
      (fun k => Matrix.of fun b a =>
      if k then (if b = a then 0 else if b then ((-Real.sin ((v - u) / 2) : ℝ) : ℂ)
        else ((-Real.cos ((u + v) / 2) : ℝ) : ℂ))
      else (if b = a then (if b then (Real.sin ((u + v) / 2) : ℂ)
        else (Real.cos ((v - u) / 2) : ℂ)) else 0) : Bool → Matrix Bool Bool ℂ) := by
    have e1 : (v - Real.pi / 2 + (u - Real.pi / 2)) / 2 = (u + v) / 2 - Real.pi / 2 := by ring
    have e2 : (u - Real.pi / 2 - (v - Real.pi / 2)) / 2 = -((v - u) / 2) := by ring
    funext k b a
    simp only [canonicalKraus, Matrix.of_apply, e1, e2, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
      Real.cos_neg, Real.sin_neg]
  have p1 := Real.sin_sq_add_cos_sq ((u + v) / 2)
  have p2 := Real.sin_sq_add_cos_sq ((v - u) / 2)
  rw [show rankTwoQubitMap (v - Real.pi / 2) (u - Real.pi / 2) =
    QAlgorithms.krausApply (canonicalKraus (v - Real.pi / 2) (u - Real.pi / 2)) from rfl, hK']
  have hK : canonicalKraus u v = (fun k => Matrix.of fun b a => if k then
      (if b = a then 0 else if b then (Real.sin ((v-u)/2) : ℂ) else (Real.sin ((u+v)/2) : ℂ))
      else (if b = a then (if b then (Real.cos ((u+v)/2) : ℂ) else (Real.cos ((v-u)/2) : ℂ))
      else 0) : Bool → Matrix Bool Bool ℂ) := by
    funext k b a; rfl
  rw [hK]
  generalize Real.sin ((u + v) / 2) = s2 at *
  generalize Real.cos ((u + v) / 2) = c2 at *
  generalize Real.sin ((v - u) / 2) = s1 at *
  generalize Real.cos ((v - u) / 2) = c1 at *
  have p1' : (s2 : ℂ) ^ 2 + (c2 : ℂ) ^ 2 = 1 := by exact_mod_cast p1
  have p2' : (s1 : ℂ) ^ 2 + (c1 : ℂ) ^ 2 = 1 := by exact_mod_cast p2
  constructor
  · ext i j
    cases i <;> cases j <;>
    simp [QAlgorithms.IsKrausFamily, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.conj_ofReal, Fintype.sum_bool] <;>
    first
      | linear_combination p1'
      | linear_combination p2'
  · funext ρ
    ext i j
    cases i <;> cases j <;>
    simp [complementaryChannel, QAlgorithms.traceLeft, indexedKrausDilation,
      QAlgorithms.krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Complex.conj_ofReal, Fintype.sum_bool] <;>
    ring
