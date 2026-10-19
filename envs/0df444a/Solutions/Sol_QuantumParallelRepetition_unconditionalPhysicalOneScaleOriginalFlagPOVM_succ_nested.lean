-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhysicalOneScaleOriginalFlagPOVM_succ_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/7fb8a14c-3d99-426d-b298-68812bf3048b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPhysicalOneScaleActualGlobalFiberPOVM_nested

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
    {C Z : Type*} [Fintype C] [DecidableEq C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (default : C)
    (source : Z → POVM C (Fin d))
    (j : Fin L) (x : Z) :
    physical8OneScaleOriginalFlagPOVM
        (N := N) (d := d) (m := m) phaseSplit default source
        j.succ x =
      directDSVActualReindexedRetainedPOVM
        (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
          phaseSplit j)
        (directDSVActualReindexedRetainedPOVM
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (source x)) := by
  change
    directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j) (source x) = _
  exact unconditionalPhysicalOneScaleActualGlobalFiberPOVM_nested
    phaseSplit j (source x)
end QuantumParallelRepetition
