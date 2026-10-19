-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/b3e6e003-5d9d-43d3-bbbb-e7034f19d554

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
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} {w : ℝ} (width : 0 < w) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    dSVDensityRationalCanonicalAcceptedCoefficient
        w N ξ i ^ 2 =
      w * ((dSVDensityRationalPhysicalAcceptedRank
        w N ξ i).val : ℝ) / (N : ℝ) := by
  rw [dSVDensityRationalCanonicalAcceptedCoefficient_sq
    width N ξ i,
    dSVDensityRationalPhysicalAcceptedRank_gridPrefix]
  ring
end QuantumParallelRepetition
