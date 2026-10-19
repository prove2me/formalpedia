-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualCommonStopPhysicalState_eq_outcomeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/5bb9c73c-e9b1-4b69-aab1-e4d00e86120c

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
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex
        (L + 1) N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨j.succ, alice⟩, ⟨j.succ, bob⟩) =
      ∏ i : Fin (L + 1),
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j i (alice i, bob i) := by
  exact
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
      width schedule ξ ζ j.succ j.succ alice bob
end QuantumParallelRepetition
