-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalPrefixMask_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/f89d1949-3b5e-4f17-bcf9-22f283ec6d0e

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
    (dSVDensityRationalCanonicalPrefixMask
      w N ξ).transpose =
      dSVDensityRationalCanonicalPrefixMask w N ξ := by
  classical
  simp [dSVDensityRationalCanonicalPrefixMask]
end QuantumParallelRepetition
