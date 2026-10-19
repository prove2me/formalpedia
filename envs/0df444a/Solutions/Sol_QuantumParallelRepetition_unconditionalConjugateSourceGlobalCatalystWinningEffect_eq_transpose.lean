-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/55f29de0-3b8a-4820-bf98-3009c5fca48e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugatePOVM_jointEffect

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    unconditionalConjugateSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y =
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y).transpose := by
  classical
  unfold unconditionalConjugateSourceGlobalCatalystWinningEffect
    exactSourceGlobalCatalystWinningEffect
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact unconditionalConjugatePOVM_jointEffect
      (exactSourceGlobalCatalystAlicePOVM G n S D e a₀ x)
      (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y)
      a b
  · exact Matrix.transpose_zero.symm
end QuantumParallelRepetition
