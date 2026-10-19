-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedThreshold_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/df41778d-efaf-4838-b5a0-5e9767933699

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalMixedAcceptedThreshold_iff

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
    (i j : Fin d) :
    (Finset.univ.filter fun k : Fin N =>
      dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) = true ∧
        dSVDensityRationalProjectiveThresholdBin w N k
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ζ).isHermitian.eigenvalues j) = true).card =
      (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val := by
  let rank :=
    dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j
  have bound : rank.val ≤ N := by
    have actual := rank.isLt
    omega
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true) =
        Finset.univ.filter fun k : Fin N => k.val < rank.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
      width grid ξ ζ i j k
  rw [same, Fin.card_filter_val_lt, min_eq_right bound]
end QuantumParallelRepetition
