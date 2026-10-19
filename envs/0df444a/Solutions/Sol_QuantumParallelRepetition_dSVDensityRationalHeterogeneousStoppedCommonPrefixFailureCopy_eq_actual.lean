-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/0098e6ac-524a-4879-9f54-933fd7806ca5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before

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
    (j : Fin L) (i : Fin j.val) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        (N := N) width schedule ξ ζ j i =
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j
        ⟨i.val, by omega⟩ := by
  symm
  exact
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before
      width schedule ξ ζ j ⟨i.val, by omega⟩ i.isLt
end QuantumParallelRepetition
