-- Prove2me | solution 1 for WolfAreaLaw.local_expectations_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:37:55.19724+00:00
-- url     : https://prove2.me/submissions/96af9132-521e-4db0-8d15-b38cd425237a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement

open scoped Kronecker

theorem solution {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.trace = 1)
    (HA : Matrix A A ℂ) (HB : Matrix B B ℂ) :
    ((HA ⊗ₖ (1 : Matrix B B ℂ)) * (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ)).trace =
        ((HA ⊗ₖ (1 : Matrix B B ℂ)) * ρ).trace ∧
      (((1 : Matrix A A ℂ) ⊗ₖ HB) * (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ)).trace =
        (((1 : Matrix A A ℂ) ⊗ₖ HB) * ρ).trace := by
  have hB : (QAlgorithms.traceLeft ρ).trace = 1 := by
    rw [← hρ]
    simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceLeft, Matrix.of_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hA : (QAlgorithms.traceRight ρ).trace = 1 := by
    rw [← hρ]
    simp only [Matrix.trace, Matrix.diag, QAlgorithms.traceRight, Matrix.of_apply,
      Fintype.sum_prod_type]
  constructor
  · rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, one_mul, hB, mul_one]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.traceRight,
      Matrix.of_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  · rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, one_mul, hA, one_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, QAlgorithms.traceLeft,
      Matrix.of_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    calc ∑ x : B, ∑ y : B, ∑ i : A, HB x y * ρ (i, y) (i, x)
        = ∑ x : B, ∑ i : A, ∑ y : B, HB x y * ρ (i, y) (i, x) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ i : A, ∑ x : B, ∑ y : B, HB x y * ρ (i, y) (i, x) := Finset.sum_comm
