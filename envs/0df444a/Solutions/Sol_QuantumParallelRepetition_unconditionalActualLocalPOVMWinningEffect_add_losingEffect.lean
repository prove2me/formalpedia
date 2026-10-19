-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualLocalPOVMWinningEffect_add_losingEffect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/285760e5-a3aa-4ff8-bb7f-93d3a8668094

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G PA PB x y +
      unconditionalActualLocalPOVMLosingEffect G PA PB x y = 1 := by
  classical
  change
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true
      then PA.effect a ⊗ₖ PB.effect b else 0) +
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true
        then 0 else PA.effect a ⊗ₖ PB.effect b) = 1
  calc
    _ = ∑ a : A, ∑ b : B, PA.effect a ⊗ₖ PB.effect b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      split <;> simp
    _ = (∑ a : A, PA.effect a) ⊗ₖ
          (∑ b : B, PB.effect b) := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [PA.complete, PB.complete]
      exact Matrix.one_kronecker_one
end QuantumParallelRepetition
