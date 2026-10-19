-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualC485RetainedPureWorkReindexBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/98516425-da17-467a-aae9-be2e55fa6269

import Mathlib
import Definitions.Def_QuantumParallelRepetition
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
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {s t v : Type}
    [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    [Fintype v] [DecidableEq v]
    (e : t ≃ v)
    (winning : Matrix s s ℂ)
    (z : EuclideanSpace ℂ (s × t)) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix t t ℂ))) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := s × v) (𝕜 := ℂ)
          (winning ⊗ₖ (1 : Matrix v v ℂ)))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.prodCongr (Equiv.refl s) e) z) := by
  classical
  let whole : s × t ≃ s × v :=
    Equiv.prodCongr (Equiv.refl s) e
  have actual_identity :
      Matrix.reindex whole.symm whole.symm
          (winning ⊗ₖ (1 : Matrix v v ℂ)) =
        winning ⊗ₖ (1 : Matrix t t ℂ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases same : a = b
    · subst b
      simp [whole, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
    · have different : e a ≠ e b := fun h => same (e.injective h)
      simp [whole, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
        same, different]
  rw [← actual_identity]
  exact directDSVActualReindexedWinningEffect_quadratic
    whole (winning ⊗ₖ (1 : Matrix v v ℂ)) z
end QuantumParallelRepetition
