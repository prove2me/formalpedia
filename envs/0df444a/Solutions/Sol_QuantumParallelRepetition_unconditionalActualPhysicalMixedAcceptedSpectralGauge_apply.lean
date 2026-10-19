-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/d7bab1d3-4e5d-4e59-9187-c1c9d76b2d32

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
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {B N d m : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    (unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) U :
        Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
          (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)
      ⟨(φ, i), finProdFinEquiv (k, a)⟩
      ⟨(ψ, j), finProdFinEquiv (l, b)⟩ =
        if φ = ψ then
          (U : Matrix
              (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ)
            ⟨k, i⟩ ⟨l, j⟩ *
            (if a = b then (1 : ℂ) else 0)
        else 0 := by
  classical
  have threshold_a : (finProdFinEquiv (k, a)).divNat = k := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).1 = k
    rw [Equiv.symm_apply_apply]
  have harmonic_a : (finProdFinEquiv (k, a)).modNat = a := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).2 = a
    rw [Equiv.symm_apply_apply]
  have threshold_b : (finProdFinEquiv (l, b)).divNat = l := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).1 = l
    rw [Equiv.symm_apply_apply]
  have harmonic_b : (finProdFinEquiv (l, b)).modNat = b := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).2 = b
    rw [Equiv.symm_apply_apply]
  simp [unconditionalActualCleanedSelectedStageSpectralUnitary,
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    unconditionalActualCleanedSelectedStagePhysicalIndexEquiv,
    coherentSharedRandomControlledUnitary,
    unconditionalActualCleanedSelectedTensorUnitary,
    Matrix.blockDiagonal'_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, threshold_a, harmonic_a,
    threshold_b, harmonic_b]
end QuantumParallelRepetition
