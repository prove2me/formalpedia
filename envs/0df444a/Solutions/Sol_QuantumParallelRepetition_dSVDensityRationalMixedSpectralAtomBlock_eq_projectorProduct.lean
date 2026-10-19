-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_eq_projectorProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/42ad320a-ba31-4390-a5f5-02b099dff246

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
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Bool) (k : Fin N) :
    dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k =
      (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ξ).effect a *
        (dSVDensityRationalLeftProjectiveThresholdPOVM
          w N k ζ).effect b := by
  classical
  unfold dSVDensityRationalMixedSpectralAtomBlock
    dSVDensityRationalLeftProjectiveThresholdPOVM
    dSVDensityRationalProjectiveThresholdPOVM
    spectralPartitionPOVM
  simp only [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases alice : dSVDensityRationalProjectiveThresholdBin w N k
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).isHermitian.eigenvalues i) = a
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp [alice, bob]
    · simp [alice, bob]
  · by_cases bob : dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = b
    · simp [alice, bob]
    · simp [alice, bob]
end QuantumParallelRepetition
