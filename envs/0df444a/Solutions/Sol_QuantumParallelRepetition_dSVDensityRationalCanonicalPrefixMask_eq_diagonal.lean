-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalPrefixMask_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/2e4130d8-a03c-476a-a981-67134438264a

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
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalPrefixMask w N ξ =
      Matrix.diagonal
        (fun q : DSVUniformDensityThresholdLocalIndex N d =>
          if dSVDensityRationalProjectiveThresholdBin w N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues q.2) = true
          then (1 : ℂ) else 0) := by
  unfold dSVDensityRationalCanonicalPrefixMask
  rw [Matrix.blockDiagonal'_diagonal]
end QuantumParallelRepetition
