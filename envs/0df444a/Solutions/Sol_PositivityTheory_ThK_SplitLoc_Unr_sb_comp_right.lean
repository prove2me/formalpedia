-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.sb_comp_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:47.021134+00:00
-- url     : https://prove2.me/submissions/e75001c3-c17a-48bf-a70b-3e7fce824457

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {X : Matrix A D k}
    {R : Matrix D A k} (hXR : X * R = 1) {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB _) :
    (fun g : Matrix A A k => Φ (g * X)) ∈ SB _ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨hl, hc⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have h1 : Continuous fun g : Matrix A A k => g * X := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun Y : Matrix A D k => Y * R := continuous_id.matrix_mul continuous_const
  have hli : Function.LeftInverse (fun Y : Matrix A D k => Y * R) (fun g : Matrix A A k => g * X) := fun g => by
    simp only [Matrix.mul_assoc, hXR, Matrix.mul_one]
  exact ⟨hl.comp_continuous h1, hc.comp_isClosedEmbedding (hli.isClosedEmbedding h2 h1)⟩
end PositivityTheory.ThK.SplitLoc.Unr
