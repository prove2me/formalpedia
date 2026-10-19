-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/857d89bf-6078-44f3-939a-5d6121ccc88d

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
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ dSVDensityRationalCanonicalAcceptedCoefficient
      w N ξ i := Real.sqrt_nonneg _
end QuantumParallelRepetition
