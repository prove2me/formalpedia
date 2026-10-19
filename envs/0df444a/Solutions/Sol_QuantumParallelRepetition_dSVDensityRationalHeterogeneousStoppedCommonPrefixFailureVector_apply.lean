-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/a074a660-6dc0-4518-93bd-ab6441422de0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (q : Fin j.val →
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d)) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        width schedule ξ ζ j q =
      ∏ i : Fin j.val,
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          ⟨i.val, by omega⟩ (q i) := by
  change
    (∏ i : Fin j.val,
      dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        width schedule ξ ζ j i (q i)) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual]
end QuantumParallelRepetition
