-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.one_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:17.514808+00:00
-- url     : https://prove2.me/submissions/9aa834eb-4490-4cf1-afa1-c9565a921971

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_ind
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_prod
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution : one κ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  refine ⟨lc_prod _ fun p _ => (lc_ind one_ne_zero).comp_continuous (continuous_apply p), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k 1))
    fun x hx => ?_
  by_contra h
  exact hx fun p _ => ind_ne (Finset.prod_ne_zero_iff.1 h p (Finset.mem_univ _))
end PositivityTheory.ThKG.Std
