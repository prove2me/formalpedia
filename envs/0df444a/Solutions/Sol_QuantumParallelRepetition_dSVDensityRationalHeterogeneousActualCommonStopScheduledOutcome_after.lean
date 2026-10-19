-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/80bccdf3-4a46-4422-8a43-8ed153b499c5

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
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1))
    (after : j.val < i.val) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j i =
      dSVUniformDensityThresholdSharedState N d := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_after
    j i after]
  exact dSVDensityRationalCompleteStoppedOptionalOutcome_none_none
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
      width schedule i) N ξ ζ
end QuantumParallelRepetition
