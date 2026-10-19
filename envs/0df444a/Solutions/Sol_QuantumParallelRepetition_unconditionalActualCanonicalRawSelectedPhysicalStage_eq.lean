-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualCanonicalRawSelectedPhysicalStage_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/540f041b-396f-4e8a-8c83-df589bfa426d

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
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    unconditionalActualCanonicalRawSelectedPhysicalStage
        (B := B) (N := N) (m := m) w ξ ζ =
      unconditionalActualPhysicalMixedAcceptedRawStage
        (B := B) (N := N) (m := m) w ξ ζ := by
  rfl
end QuantumParallelRepetition
