-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.p_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:41.056272+00:00
-- url     : https://prove2.me/submissions/fd2daff6-9488-45ae-a768-8374a1e505bd

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_const_mul
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_mul_transpose
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_wt_ne_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitFlip_apow_inv
import Theorems.Thm_GlobalTheory_SplitFlip_omA_mem_SB
import Theorems.Thm_GlobalTheory_SplitFlip_omA_mul
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
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) :
    ∀ Φ ∈ SB _, ∀ g, pUnr a a' ϖ ν β (omA ν β g 1 Φ) = pUnr a a' ϖ ν β Φ := by
  intro Φ hΦ g
  funext h
  have e1 : omA ν β 1 h (omA ν β g 1 Φ) = omA ν β g 1 (omA ν β 1 h Φ) := by
    rw [← omA_mul, ← omA_mul, one_mul, mul_one, mul_one, one_mul]
  have hΦ' := omA_mem_SB ν β 1 h hΦ
  have e2 : (fun x : Matrix (Fin a) (Fin a) k => omA ν β g 1 (omA ν β 1 h Φ) (x * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) =
      fun x => wt (a + a') ν g⁻¹ * (fun y => omA ν β 1 h Φ (y * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ((g⁻¹).val * x) := by
    funext x
    simp only [omA, wt, map_one, map_inv, Units.val_inv_eq_inv_val, Units.val_one, apow_one, apow_inv, mul_one,
      Fintype.card_fin, Matrix.mul_one, Matrix.mul_assoc]
    congr 1
    rw [neg_div]
  unfold pUnr
  rw [e1]
  refine (congrArg (zetaUnr a (a + a') ϖ ν) e2).trans ?_
  rw [zetaUnr_const_mul, zetaUnr_mul_left hS.unif hν _ _ (sb_comp_right (upperProjection_mul_transpose _) hΦ') g⁻¹,
    ← mul_assoc, mul_inv_cancel₀ (wt_ne_zero _ _ _), one_mul]
  rfl
end PositivityTheory.ThK.SplitLoc.Unr
