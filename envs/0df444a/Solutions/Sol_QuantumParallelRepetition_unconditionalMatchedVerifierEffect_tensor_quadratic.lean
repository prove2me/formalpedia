-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedVerifierEffect_tensor_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/152a7809-838a-494e-8788-ffd602ffcc2c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_expand

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ)))
      (unconditionalMatchedVerifierTensor target work) =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) effect)
          target := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_complex :
      (∑ k : t, work k * star (work k)) =
        (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ k : t, work k * star (work k)) =
          (↑(∑ k : t, ‖work k‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro k _
            simpa [Complex.normSq_eq_norm_sq] using
              Complex.mul_conj (work k)
      _ = (↑(‖work‖ ^ 2) : ℂ) := by
            rw [← EuclideanSpace.norm_sq_eq]
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (effect i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (target j.1 * work j.2)) *
        star (target i.1 * work i.2)).re =
      ‖work‖ ^ 2 *
        (∑ i : s, (∑ j : s, effect i j * target j) *
          star (target i)).re
  rw [Fintype.sum_prod_type]
  have complex_factor :
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        ∑ i : s, ∑ k : t,
          ((∑ j : s, effect i j * target j) * work k) *
            star (target i * work k) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              rw [Fintype.sum_prod_type]
              simp [mul_ite, ite_mul, Finset.sum_mul, mul_assoc]
      _ = ∑ i : s,
        ((∑ j : s, effect i j * target j) * star (target i)) *
          (∑ k : t, work k * star (work k)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            simp only [star_mul]
            ring
      _ = (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
            rw [residual_complex, Finset.sum_mul]
  rw [complex_factor, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring
end QuantumParallelRepetition
