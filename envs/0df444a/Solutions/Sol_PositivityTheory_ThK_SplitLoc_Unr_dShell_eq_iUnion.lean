-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.dShell_eq_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:26.144824+00:00
-- url     : https://prove2.me/submissions/0b60e99e-378b-4624-b87c-eb882be0073a

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_shellSet_eq_cell
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_of_mem_shellSet
import Theorems.Thm_GlobalTheory_GLDoubling_iUnion_cell
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (m : ℤ) :
    dShell (k := k) n m = ⋃ e : {e : Fin n → ℤ // Antitone e ∧ ∑ i, e i = m}, shellSet ϖ e.1 := by
  ext g
  rw [Set.mem_iUnion]
  constructor
  · intro hg
    have h : g ∈ ⋃ e : {e : Fin n → ℤ // Antitone e}, GlobalTheory.GLDoubling.cell k (Fin n) ϖ e := by
      rw [GlobalTheory.GLDoubling.iUnion_cell hϖ]; trivial
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 h
    rw [← shellSet_eq_cell] at he
    exact ⟨⟨e.1, e.2, (ord_of_mem_shellSet hϖ he).symm.trans hg⟩, he⟩
  · rintro ⟨e, he⟩
    exact (ord_of_mem_shellSet hϖ he).trans e.2.2
end PositivityTheory.ThK.SplitLoc.Unr
