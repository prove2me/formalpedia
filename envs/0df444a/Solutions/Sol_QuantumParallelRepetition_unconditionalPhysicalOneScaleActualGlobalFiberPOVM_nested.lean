-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhysicalOneScaleActualGlobalFiberPOVM_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/64f521b3-9fb9-4fad-8b54-1d346f85ab5f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualRetainedPOVM_ext

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {C : Type*} [Fintype C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (j : Fin L)
    (source : POVM C (Fin d)) :
    directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j) source =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          phaseSplit j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          source) := by
  classical
  apply unconditionalActualRetainedPOVM_ext
  intro a i k
  let outer :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        1 P N d L m ≃
        UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R :=
    unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j
  let inner :
      UnconditionalSelectedCopyLocalIndex P d N m ≃
        Fin d × (Fin P × Fin (N * m)) :=
    physical8SelectedGlobalTargetWorkEquiv P N d m
  by_cases selected :
      (inner (outer i).1).2 = (inner (outer k).1).2
  · by_cases retained : (outer i).2 = (outer k).2
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
  · by_cases retained : (outer i).2 = (outer k).2
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
    · simp [directDSVActualReindexedRetainedPOVM_effect,
        physical8OneScaleActualGlobalFiberEquiv,
        Equiv.prodAssoc_apply, outer, inner, selected, retained]
end QuantumParallelRepetition
