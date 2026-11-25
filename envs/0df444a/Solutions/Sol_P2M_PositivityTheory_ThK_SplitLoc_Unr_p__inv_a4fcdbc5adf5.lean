-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SplitLoc_Unr_p__inv_a4fcdbc5adf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:29:22.966596+00:00
-- url     : https://prove2.me/submissions/40dc8200-d5bf-4f44-a717-0ba59e15ac3c

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_const_mul
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_lowerProjection_mul_right_inverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_wt_ne_zero
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_invT
import Theorems.Thm_GlobalTheory_SplitFlip_invT_inv_val
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
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) :
    ∀ Ψ ∈ SB _, ∀ g, pUnr' a a' ϖ ν α (omB ν α g 1 Ψ) = pUnr' a a' ϖ ν α Ψ := by
  intro Ψ hΨ g
  funext h
  have hΨ' := omB_mem_SB ν α g 1 hΨ
  have hg : gdet (invT g)⁻¹ = gdet g := by
    rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
  have e2 : (fun x : Matrix (Fin a') (Fin a') k => omB ν α g 1 Ψ (x * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) =
      fun x => wt (a + a') ν (invT g)⁻¹ * (fun y => Ψ (y * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) (((invT g)⁻¹).val * x) := by
    funext x
    simp only [omB, wt, hg, invT_inv_val, map_one, Units.val_one, apow_one, mul_one, Fintype.card_fin,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [pUnr'_eq hS hν hΨ', pUnr'_eq hS hν hΨ, e2, zetaUnr_const_mul,
    zetaUnr_mul_left hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ) (invT g)⁻¹,
    ← mul_assoc (wt _ _ _), mul_inv_cancel₀ (wt_ne_zero _ _ _), one_mul]
end PositivityTheory.ThK.SplitLoc.Unr
