-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/af06c9db-a110-402c-824c-310df5e5a151

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
    (before : i.val < j.val) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j i =
      dSVDensityRationalCompleteProjectiveOutcome
        (width (schedule
          ⟨i.val, lt_trans before j.isLt⟩))
        N ξ ζ false false := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_before
    j i before]
  rw [dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
  simp [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth,
    lt_trans before j.isLt]
end QuantumParallelRepetition
