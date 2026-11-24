-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.upperProjection_inverse_transpose_right_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:03.278796+00:00
-- url     : https://prove2.me/submissions/4b4bf352-d39e-44f2-9ed5-cf2af221323f

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_mul_transpose
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_invT_mul_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val : Matrix (Fin a) (Fin (a + a')) k) *
      (h.valᵀ * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))ᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (invT h).val, invT_mul_transpose, Matrix.one_mul, upperProjection_mul_transpose]
end PositivityTheory.ThK.SplitLoc.Unr
