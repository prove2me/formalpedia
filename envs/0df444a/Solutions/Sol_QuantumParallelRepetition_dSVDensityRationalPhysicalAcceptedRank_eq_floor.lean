-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_eq_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/ddf082fd-7431-44a1-8a03-796b798394e1

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVDensityRationalPhysicalAcceptedRank
      w N ξ i).val =
      Nat.floor
        (dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
  have unit := dSVRationalSoftPass_mem_unit width
    ((dSVSoftBobLeftReducedDensity_posSemidef
      ξ).eigenvalues_nonneg i)
  simpa [dSVDensityRationalPhysicalAcceptedRank,
    dSVDensityRationalProjectiveThresholdBin] using
    (dSVUniformDensityThresholdGrid_count_eq_floor grid
      (dSVRationalSoftPass w
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i)) unit.1 unit.2)
end QuantumParallelRepetition
