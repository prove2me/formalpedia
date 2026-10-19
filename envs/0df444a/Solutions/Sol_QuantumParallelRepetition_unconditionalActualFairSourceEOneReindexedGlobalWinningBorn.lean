-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/fa69af2c-af0a-4085-96cf-6b7085466a88

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_directDSVActualReindexedWinningEffect_quadratic
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex

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
    {d : ℕ}
    (winning :
      Matrix (Fin (d * 1) × Fin (d * 1))
        (Fin (d * 1) × Fin (d * 1)) ℂ)
    (ξ : BipartiteUnitVector d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
        (Matrix.reindex
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d)))
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d))) winning))
      (unconditionalConjugatePureVector ξ.val) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ)) := by
  classical
  let e : (Fin (d * 1) × Fin (d * 1)) ≃ (Fin d × Fin d) :=
    Equiv.prodCongr (finCongr (Nat.mul_one d))
      (finCongr (Nat.mul_one d))
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
          (unconditionalConjugatePureVector ξ.val)) := by
          exact directDSVActualReindexedWinningEffect_quadratic
            e.symm winning
            (unconditionalConjugatePureVector ξ.val)
    _ = _ := by
          congr 1
          exact
            unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
              ξ
end QuantumParallelRepetition
