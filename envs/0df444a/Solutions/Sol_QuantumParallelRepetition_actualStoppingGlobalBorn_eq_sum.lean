-- Prove2me | solution 1 for QuantumParallelRepetition.actualStoppingGlobalBorn_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/9e8d2ab0-734e-4d22-961d-cbb09ff4d4fa

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixQuadraticExpectation_expand
import Theorems.Thm_QuantumParallelRepetition_actualStoppingGlobalWinningEffect_same
import Theorems.Thm_QuantumParallelRepetition_actualStoppingGlobalWinningEffect_cross_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (x : X) (y : Y) :
    quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ s, κ s)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect G PA PB x y)) z =
      ∑ r : R, ∑ s : R,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB r s x y))
          (actualStoppingBranchVector z r s) := by
  classical
  have collapse (r s : R) (i : ι r) (j : κ s) :
      (∑ r' : R, ∑ i' : ι r', ∑ s' : R, ∑ j' : κ s',
        actualStoppingGlobalWinningEffect G PA PB x y
            (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) *
          z (⟨r', i'⟩, ⟨s', j'⟩)) =
        ∑ i' : ι r, ∑ j' : κ s,
          actualStoppingBranchWinningEffect G PA PB r s x y
              (i, j) (i', j') * z (⟨r, i'⟩, ⟨s, j'⟩) := by
    rw [Finset.sum_eq_single r]
    · apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.sum_eq_single s]
      · apply Finset.sum_congr rfl
        intro j' _
        rw [actualStoppingGlobalWinningEffect_same]
      · intro s' _ unequal
        apply Finset.sum_eq_zero
        intro j' _
        rw [actualStoppingGlobalWinningEffect_cross_eq_zero
          G PA PB r s r s' x y i j i' j'
            (Or.inr (Ne.symm unequal))]
        simp
      · simp
    · intro r' _ unequal
      apply Finset.sum_eq_zero
      intro i' _
      apply Finset.sum_eq_zero
      intro s' _
      apply Finset.sum_eq_zero
      intro j' _
      rw [actualStoppingGlobalWinningEffect_cross_eq_zero
        G PA PB r s r' s' x y i j i' j'
          (Or.inl (Ne.symm unequal))]
      simp
    · simp
  rw [matrixQuadraticExpectation_expand]
  simp_rw [matrixQuadraticExpectation_expand]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [collapse]
  rfl
end QuantumParallelRepetition
