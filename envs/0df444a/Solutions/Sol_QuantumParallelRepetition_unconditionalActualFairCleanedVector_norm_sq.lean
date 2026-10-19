-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairCleanedVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/af4d0bcc-f5a7-49fa-8777-64cde2d67af1

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
import Theorems.Thm_QuantumParallelRepetition_integratorActualCanonicalRetainedPhaseTail_norm
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSelectedLocalAction_norm_sq

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
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  letI : DecidableEq
      (IntegratorActualC485RetainedIndex S B N d L j) :=
    FinEnum.decEq
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualFairSelectedLocalAction_norm_sq]
  exact unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    phases grid harmonic width width_positive schedule ξ ζ Q A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)
end QuantumParallelRepetition
