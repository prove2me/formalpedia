-- Prove2me | solution 1 for QuantumParallelRepetition.residualIdentity_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/0a96ef5b-01cf-45a2-823a-f836addb6ac0

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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {s t : Type} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (M : Matrix s s ℂ)
    (z : EuclideanSpace ℂ s)
    (κ : EuclideanSpace ℂ t)
    (normalized : ‖κ‖ = 1) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (M ⊗ₖ (1 : Matrix t t ℂ)))
      (toLp 2 (fun q : s × t => z q.1 * κ q.2)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_square :
      (∑ j : t, ‖κ j‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, normalized]
    norm_num
  have residual_complex :
      (∑ j : t, κ j * star (κ j)) = 1 := by
    calc
      (∑ j : t, κ j * star (κ j)) =
          (↑(∑ j : t, ‖κ j‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro j _
            simpa [Complex.normSq_eq_norm_sq] using
              Complex.mul_conj (κ j)
      _ = 1 := by rw [residual_square]; norm_num
  congr 1
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (M i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i.1 * κ i.2)) =
      ∑ i : s, (∑ j : s, M i j * z j) * star (z i)
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : s, ∑ k : t,
      (∑ j : s × t,
        (M i j.1 * (if k = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i * κ k)) =
      ∑ i : s, ∑ k : t,
        ((∑ j : s, M i j * z j) * κ k) *
          star (z i * κ k) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            rw [Fintype.sum_prod_type]
            simp [mul_ite, ite_mul, Finset.sum_mul, mul_assoc]
    _ = ∑ i : s,
      ((∑ j : s, M i j * z j) * star (z i)) *
        (∑ k : t, κ k * star (κ k)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [star_mul]
          ring
    _ = ∑ i : s, (∑ j : s, M i j * z j) * star (z i) := by
          rw [residual_complex]
          simp
end QuantumParallelRepetition
