-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.summable_geom_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:59.865155+00:00
-- url     : https://prove2.me/submissions/0a7c91b2-46b1-4ca4-a0cf-502f33b43f0c

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_coeff_prod_geom
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_geom_iff
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_prod
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
open PowerSeries
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ < 1) :
    Summable fun t : ℕ => ‖∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i‖ := by
  have h := GlobalTheory.CompleteHomogeneousBound.weightedSummable_prod 1 Finset.univ
    (fun i => (mk fun t => γ i ^ t : PowerSeries ℂ))
    (fun i _ => (GlobalTheory.CompleteHomogeneousBound.weightedSummable_geom_iff 1 (γ i)).mpr (by simpa using hγ i))
  unfold GlobalTheory.CompleteHomogeneousBound.WeightedSummable at h
  simpa [GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom] using h
end PositivityTheory.ThK.SplitLoc.Unr
