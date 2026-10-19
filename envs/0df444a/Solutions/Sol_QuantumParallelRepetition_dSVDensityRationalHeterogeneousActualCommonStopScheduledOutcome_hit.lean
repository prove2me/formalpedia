-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/7a95311c-a178-433e-ba29-0882b73912b6

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
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j j.castSucc =
      dSVDensityRationalCompleteProjectiveOutcome
        (width (schedule j)) N ξ ζ true true := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit]
  rw [dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
  simp [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth]
end QuantumParallelRepetition
