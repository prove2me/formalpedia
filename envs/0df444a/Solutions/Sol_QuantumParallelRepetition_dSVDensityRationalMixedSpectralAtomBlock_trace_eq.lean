-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedSpectralAtomBlock_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/449e200a-4b58-4e59-b875-9cb8d6ba5169

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
    (Matrix.trace
      (dSVDensityRationalMixedSpectralAtomBlock
        w N ξ ζ a b k)).re =
      ∑ i : Fin d, ∑ j : Fin d,
        if dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = a ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = b
        then spectralAtomOverlap
          (dSVSoftBobLeftReducedDensity ξ)
          (dSVSoftBobLeftReducedDensity ζ)
          (dSVSoftBobLeftReducedDensity_posSemidef ξ)
          (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j
        else 0 := by
  unfold dSVDensityRationalMixedSpectralAtomBlock
  simp only [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [spectralAtomOverlap]
end QuantumParallelRepetition
