-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/3764f9f2-d2c8-4408-b637-2e432ce2d566

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix

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
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) (k : Fin N) :
    (dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ∧
      dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ζ).isHermitian.eigenvalues j) = true) ↔
      k.val <
        (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
          w N ξ ζ i j).val := by
  rw [dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
    width grid ξ i k,
    dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
      width grid ζ j k]
  change _ ↔ k.val < min
    (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val
    (dSVDensityRationalPhysicalAcceptedRank w N ζ j).val
  omega
end QuantumParallelRepetition
