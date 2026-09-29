-- Prove2me | solution 1 for SenTachyon.backgroundField_boundary_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:53:20.646095+00:00
-- url     : https://prove2.me/submissions/54a95552-9b97-45c2-a020-403795991072

import Mathlib
import Definitions.Def_SenTachyon_Defs

set_option autoImplicit false

open SenTachyon in
theorem st_omega1_eq (R : ℝ) (y : ℝ × ℝ) :
    omega1 R y = !![Complex.exp (Complex.I * ((y.2 / R : ℝ) : ℂ)), 0;
                    0, Complex.exp (-Complex.I * ((y.2 / R : ℝ) : ℂ))] := by
  have hp : pauli3 = Matrix.diagonal ![(1 : ℂ), -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3]
  unfold omega1
  rw [hp, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

theorem st_fderiv_exp (a : ℂ) (R : ℝ) (x v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => Complex.exp (a * ((y.2 / R : ℝ) : ℂ))) x v
      = Complex.exp (a * ((x.2 / R : ℝ) : ℂ)) * (a * ((v.2 / R : ℝ) : ℂ)) := by
  set L : ℝ × ℝ →L[ℝ] ℂ :=
    a • (Complex.ofRealCLM.comp ((R⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ)) with hL
  have hLy : ∀ y : ℝ × ℝ, L y = a * ((y.2 / R : ℝ) : ℂ) := by
    intro y
    simp [L, div_eq_mul_inv, mul_comm]
  have hfun : (fun y : ℝ × ℝ => Complex.exp (a * ((y.2 / R : ℝ) : ℂ)))
      = fun y => Complex.exp (L y) := by
    funext y; rw [hLy]
  rw [hfun, (L.hasFDerivAt.cexp).fderiv]
  simp only [smul_apply, smul_eq_mul, hLy]

open SenTachyon in
theorem st_partial_omega1 (R : ℝ) (μ : Fin 2) (x : ℝ × ℝ) :
    partialDeriv μ (omega1 R) x =
      !![Complex.exp (Complex.I * ((x.2 / R : ℝ) : ℂ)) * (Complex.I * (((coordVec μ).2 / R : ℝ) : ℂ)), 0;
         0, Complex.exp (-Complex.I * ((x.2 / R : ℝ) : ℂ)) *
              (-Complex.I * (((coordVec μ).2 / R : ℝ) : ℂ))] := by
  have hfun : ∀ i j : Fin 2, (fun y => omega1 R y i j) = fun y =>
      (!![Complex.exp (Complex.I * ((y.2 / R : ℝ) : ℂ)), 0;
          0, Complex.exp (-Complex.I * ((y.2 / R : ℝ) : ℂ))] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j; funext y; rw [st_omega1_eq]
  ext i j
  simp only [partialDeriv, Matrix.of_apply]
  rw [hfun]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact st_fderiv_exp _ _ _ _
  · simp
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact st_fderiv_exp _ _ _ _

open SenTachyon in
theorem st_omega1_inv (R : ℝ) (y : ℝ × ℝ) :
    (omega1 R y)⁻¹ = !![Complex.exp (-Complex.I * ((y.2 / R : ℝ) : ℂ)), 0;
                        0, Complex.exp (Complex.I * ((y.2 / R : ℝ) : ℂ))] := by
  apply Matrix.inv_eq_left_inv
  rw [st_omega1_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_add]

open SenTachyon in
theorem solution (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) :
    ∀ (μ : Fin 2) (x₁ x₂ : ℝ),
      backgroundField R₁t R₂t μ (2 * Real.pi * R₁t, x₂)
          = gaugeTransform (omega1 R₂t) (backgroundField R₁t R₂t) μ (0, x₂) ∧
      backgroundField R₁t R₂t μ (x₁, 2 * Real.pi * R₂t)
          = gaugeTransform omega2 (backgroundField R₁t R₂t) μ (x₁, 0) := by
  intro μ x₁ x₂
  have hR1 : R₁t ≠ 0 := h₁.ne'
  have hR2 : R₂t ≠ 0 := h₂.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hE : Complex.exp (Complex.I * ((x₂ : ℂ) / (R₂t : ℂ))) * Complex.exp (-(Complex.I * ((x₂ : ℂ) / (R₂t : ℂ)))) = 1 := by
    rw [← Complex.exp_add]; simp
  constructor
  · have hA : backgroundField R₁t R₂t μ (0, x₂) = 0 := by simp [backgroundField]
    simp only [gaugeTransform, hA, mul_zero, zero_mul, zero_sub, st_partial_omega1, st_omega1_inv]
    have hV : (2 * Real.pi * (2 * Real.pi * R₁t) / torusArea R₁t R₂t : ℝ) = 1 / R₂t := by
      unfold torusArea; field_simp; ring
    fin_cases μ
    · ext i j; fin_cases i <;> fin_cases j <;> simp [backgroundField, coordVec]
    · ext i j
      fin_cases i <;> fin_cases j
      · simp only [backgroundField]
        simp [coordVec, pauli3, hV]
        linear_combination (-((R₂t : ℂ)⁻¹)) * hE + ((R₂t : ℂ)⁻¹ * Complex.exp (Complex.I * ((x₂ : ℂ) / (R₂t : ℂ))) * Complex.exp (-(Complex.I * ((x₂ : ℂ) / (R₂t : ℂ))))) * Complex.I_sq
      · simp [backgroundField, pauli3]
      · simp [backgroundField, pauli3]
      · simp only [backgroundField]
        simp [coordVec, pauli3, hV]
        linear_combination ((R₂t : ℂ)⁻¹) * hE - ((R₂t : ℂ)⁻¹ * Complex.exp (Complex.I * ((x₂ : ℂ) / (R₂t : ℂ))) * Complex.exp (-(Complex.I * ((x₂ : ℂ) / (R₂t : ℂ))))) * Complex.I_sq
  · have hd : partialDeriv μ omega2 (x₁, 0) = 0 := by
      ext i j; simp [partialDeriv, omega2]
    simp [gaugeTransform, omega2, hd, backgroundField]
