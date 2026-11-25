-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.isOpen_dShell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:50.083435+00:00
-- url     : https://prove2.me/submissions/25200116-e87d-4b95-ae19-04743df2bc1f

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_dShell_eq_iUnion
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_isOpen_shellSet
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif


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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (n : ℕ) (m : ℤ) : IsOpen (dShell (k := k) n m) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  rw [dShell_eq_iUnion hϖ]
  exact isOpen_iUnion fun e => isOpen_shellSet ϖ e.1
end PositivityTheory.ThK.SplitLoc.Unr
