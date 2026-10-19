-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceWinningEffect_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/82a67b7a-0648-4fc9-b400-d3344a6900d6

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
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A] [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (integratorActualC485SourceAlicePOVM G n S D a₀ x)
        (integratorActualC485SourceBobPOVM G n S D b₀ y)
        x y =
      Matrix.reindex
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D 1 a₀ b₀ x y) := by
  classical
  have alice_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  have bob_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases alice_instance
  cases bob_instance
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [directDSVActualLocalPOVMWinningEffect,
    integratorActualC485SourceAlicePOVM,
    integratorActualC485SourceBobPOVM,
    unconditionalConjugateSourceGlobalCatalystWinningEffect,
    reindexedPOVM, Matrix.reindex_apply,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]
end QuantumParallelRepetition
