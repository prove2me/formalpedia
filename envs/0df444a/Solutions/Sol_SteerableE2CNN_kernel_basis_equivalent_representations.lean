-- Prove2me | solution 1 for SteerableE2CNN.kernel_basis_equivalent_representations
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:40:17.619929+00:00
-- url     : https://prove2.me/submissions/88bff0ea-65ef-4516-8a16-fc985a0020fd

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic
set_option autoImplicit false
open Matrix MeasureTheory
namespace SteerableE2CNN

theorem kernel_basis_equivalent_representations (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m)
    (Pin : Matrix.GeneralLinearGroup n ℝ) (Pout : Matrix.GeneralLinearGroup m ℝ)
    (k : Plane → Matrix m n ℝ) :
    IsSteerable G ρin ρout k ↔
      KernelConstraint (fun g : G => gMat g)
        (fun g => (↑Pout⁻¹ : Matrix m m ℝ) * repMat ρout g * (↑Pout : Matrix m m ℝ))
        (fun g => (↑Pin⁻¹ : Matrix n n ℝ) * repMat ρin g * (↑Pin : Matrix n n ℝ))
        (fun x => (↑Pout⁻¹ : Matrix m m ℝ) * k x * (↑Pin : Matrix n n ℝ)) := by
  set A : Matrix m m ℝ := ↑Pout⁻¹ with hA
  set B : Matrix m m ℝ := ↑Pout with hB
  set C : Matrix n n ℝ := ↑Pin⁻¹ with hC
  set D : Matrix n n ℝ := ↑Pin with hD
  have hAB : A * B = 1 := Pout.inv_mul
  have hBA : B * A = 1 := Pout.mul_inv
  have hCD : C * D = 1 := Pin.inv_mul
  have hDC : D * C = 1 := Pin.mul_inv
  have hDi : D⁻¹ = C := Matrix.inv_eq_left_inv hCD
  have hCi : C⁻¹ = D := Matrix.inv_eq_left_inv hDC
  have key : ∀ (R : Matrix n n ℝ) (Q : Matrix m m ℝ) (K : Matrix m n ℝ),
      A * Q * B * (A * K * D) * (C * R * D)⁻¹ = A * (Q * K * R⁻¹) * D := by
    intro R Q K
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDi, hCi]
    calc A * Q * B * (A * K * D) * (C * (R⁻¹ * D))
        = A * Q * (B * A) * K * (D * C) * R⁻¹ * D := by simp only [Matrix.mul_assoc]
      _ = A * (Q * K * R⁻¹) * D := by rw [hBA, hDC]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have inj : ∀ X Y : Matrix m n ℝ, A * X * D = A * Y * D → X = Y := by
    intro X Y h
    have h2 : B * (A * X * D) * C = B * (A * Y * D) * C := by rw [h]
    calc X = (B * A) * X * (D * C) := by rw [hBA, hDC]; simp
      _ = B * (A * X * D) * C := by simp only [Matrix.mul_assoc]
      _ = B * (A * Y * D) * C := h2
      _ = (B * A) * Y * (D * C) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hBA, hDC]; simp
  unfold IsSteerable KernelConstraint
  constructor
  · intro h g x
    simp only
    rw [key, h g x]
  · intro h g x
    have := h g x
    simp only at this
    rw [key] at this
    exact inj _ _ this

end SteerableE2CNN
open SteerableE2CNN in
theorem solution (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m)
    (Pin : Matrix.GeneralLinearGroup n ℝ) (Pout : Matrix.GeneralLinearGroup m ℝ)
    (k : Plane → Matrix m n ℝ) :
    IsSteerable G ρin ρout k ↔
      KernelConstraint (fun g : G => gMat g)
        (fun g => (↑Pout⁻¹ : Matrix m m ℝ) * repMat ρout g * (↑Pout : Matrix m m ℝ))
        (fun g => (↑Pin⁻¹ : Matrix n n ℝ) * repMat ρin g * (↑Pin : Matrix n n ℝ))
        (fun x => (↑Pout⁻¹ : Matrix m m ℝ) * k x * (↑Pin : Matrix n n ℝ)) :=
  kernel_basis_equivalent_representations G ρin ρout Pin Pout k
