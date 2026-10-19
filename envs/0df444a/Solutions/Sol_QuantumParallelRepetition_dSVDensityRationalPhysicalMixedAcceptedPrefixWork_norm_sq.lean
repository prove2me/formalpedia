-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/db37744e-9037-4981-89fb-cc185fbab180

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
    (ξ ζ : BipartiteUnitVector d) (i j : Fin d) :
    ‖dSVDensityRationalPhysicalMixedAcceptedPrefixWork
        w N ξ ζ i j‖ ^ 2 =
      ((dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j).val : ℝ) := by
  exact dSVCanonicalFailurePrefix_norm_sq
    (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
      w N ξ ζ i j)
end QuantumParallelRepetition
