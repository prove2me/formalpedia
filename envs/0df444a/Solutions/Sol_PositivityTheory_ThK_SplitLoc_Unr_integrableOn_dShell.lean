-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.integrableOn_dShell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:28.267224+00:00
-- url     : https://prove2.me/submissions/f1a20a1c-6c31-498c-b7e5-bd9e63a04245

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_dShell_eq_iUnion
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_isCompact_shellSet
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_le_of_mem_shellSet
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finite_exponents
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_measurableSet_dShell
import Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
import Theorems.Thm_GlobalTheory_SBUniform_exists_bound_period
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


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
variable [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (m : ℤ) :
    IntegrableOn (fun g : GL (Fin n) k => φ g.val) (dShell n m) (haarVol (KO k (Fin n))) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨N, M, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin n) φ hφ
  have hc : Continuous fun g : GL (Fin n) k => φ g.val := hφ.1.continuous.comp Units.continuous_val
  have hK := (finite_exponents n (-(N : ℤ)) m).isCompact_biUnion fun e _ => isCompact_shellSet ϖ e
  refine (hc.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero (measurableSet_dShell n m) ?_
  rintro g ⟨hg, hg'⟩
  by_contra h
  rw [dShell_eq_iUnion hϖ] at hg
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hg
  exact hg' (Set.mem_biUnion (x := e.1) ⟨e.2.2, le_of_mem_shellSet hϖ he (hN _ h)⟩ he)
end PositivityTheory.ThK.SplitLoc.Unr
