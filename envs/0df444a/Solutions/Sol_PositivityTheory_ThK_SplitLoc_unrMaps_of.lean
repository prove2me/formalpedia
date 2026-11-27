-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.unrMaps_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:28.541106+00:00
-- url     : https://prove2.me/submissions/3314acf5-a6e9-49b6-873a-06de3be53b76

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_indicator_int_mem_SB
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_isUnram_nu
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_onto_of_irred
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_p_lin
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__lin_d70a0ddf4147
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_p_mem
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_p_inv
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_p_equiv
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__equiv_0bd955b046e5
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_p_unit
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_p__unit_84d39629c538
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_omA_mem_SB
import Theorems.Thm_GlobalTheory_SplitFlip_omB_mem_SB
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
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc
open Unr GlobalTheory.SplitFlip GlobalTheory.SplitWeil
namespace PositivityTheory.ThK.SplitLoc
theorem _root_.solution (hI : IndIrred) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irred hI hS.unitα hS.unitβ _ hp1 hp3 (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩)
      ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irred hI hS.unitα hS.unitβ _ hp2 hp4 (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩)
      ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1
end PositivityTheory.ThK.SplitLoc
