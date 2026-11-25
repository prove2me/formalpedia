-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:06:27.729254+00:00
-- url     : https://prove2.me/submissions/c3481c38-0dc8-4d53-92cd-b9b7d9df7eda

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_integral
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_norm_nu
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_lowerProjection_mul_right_inverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
variable {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ}
    (hΨ : Ψ ∈ SB _) (h : GL (Fin (a + a')) k) : pUnr' a a' ϖ ν α Ψ h = (α (gdet h) : ℂ) * apow (gdet h) ((a' : ℂ) / 2) *
      zetaUnr a' (a + a') ϖ ν (fun g => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k))) := by
  have hb := zetaUnr_eq_integral hS.unif hν (norm_nu hS ϖ) (n := a') (d := a + a') (by have := hS.lt; omega)
    (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ)
  have e : smallF (haarVol (KO k (Fin a'))) ν Ψ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val) =
      ∫ g, Ψ (g.val * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val : Matrix (Fin a') (Fin (a + a')) k)) * wt (a + a') ν g
        ∂haarVol (KO k (Fin a')) := by
    unfold smallF
    congr 1
    funext g
    simp only [wt, Fintype.card_fin]
    ring
  show (invL a' (a + a') ϖ ν).eval 1 * smallP _ _ ν α Ψ h = _
  unfold smallP
  rw [e, ← hb.2, Fintype.card_fin]
  ring
end PositivityTheory.ThK.SplitLoc.Unr
