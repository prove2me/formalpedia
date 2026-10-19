-- Prove2me | solution 1 for QuantumParallelRepetition.directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/764c7995-81cc-4e3b-b5cc-bce59d342304

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierEffect_tensor_quadratic
import Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedRetainedPOVMWinningEffect
import Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedWinningEffect_quadratic

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
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (target : EuclideanSpace ℂ (s × u))
    (work : EuclideanSpace ℂ (t × v))
    (selected :
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv eA eB) z =
          unconditionalMatchedVerifierTensor target work) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB)
          x y)) z =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s × u) (𝕜 := ℂ)
            (directDSVActualLocalPOVMWinningEffect G PA PB x y))
          target := by
  rw [directDSVActualReindexedRetainedPOVMWinningEffect,
    directDSVActualReindexedWinningEffect_quadratic,
    selected, unconditionalMatchedVerifierEffect_tensor_quadratic]
end QuantumParallelRepetition
