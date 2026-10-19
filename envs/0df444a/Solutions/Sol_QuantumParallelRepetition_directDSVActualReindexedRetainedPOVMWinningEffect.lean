-- Prove2me | solution 1 for QuantumParallelRepetition.directDSVActualReindexedRetainedPOVMWinningEffect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/9db02de1-4675-4889-9699-c1524d4479bf

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
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (directDSVActualReindexedRetainedPOVM eA PA)
        (directDSVActualReindexedRetainedPOVM eB PB)
        x y =
      Matrix.reindex
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualLocalPOVMWinningEffect G PA PB x y ⊗ₖ
          (1 : Matrix (t × v) (t × v) ℂ)) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases alice_work : (eA i).2 = (eA j).2 <;>
    by_cases bob_work : (eB k).2 = (eB l).2 <;>
      simp [directDSVActualLocalPOVMWinningEffect,
        directDSVActualReindexedRetainedPOVM,
        reindexedPOVM, purificationAlicePOVM,
        directDSVActualBilateralRetainedIndexEquiv,
        Matrix.reindex_apply, Matrix.sum_apply, Matrix.ite_apply,
        Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Equiv.prodProdProdComm_apply, alice_work, bob_work]
end QuantumParallelRepetition
