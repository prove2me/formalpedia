-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SplitLoc_Unr_p__mem_4c919705d020
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:52.966908+00:00
-- url     : https://prove2.me/submissions/9f843d07-7db7-4eb1-baa0-ff9ceff83684

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_mul_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_stab
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gdet_blkDGL
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gdet_of_isBlockUpper
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_lowerProjection_blockUpper
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_lowerProjection_mul_right_inverse
import Theorems.Thm_P2M_PositivityTheory_ThK_SplitLoc_Unr_pUnr__eq_5762b3186f8b
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_add
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
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
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hα : IsUnram α) :
    ∀ Ψ ∈ SB _, pUnr' a a' ϖ ν α Ψ ∈ indSp a a' α β := by
  intro Ψ hΨ
  refine ⟨?_, fun b h hb dA dD h1 h2 => ?_⟩
  · obtain ⟨U, hUo, hU⟩ := exists_stab hΨ
    refine ⟨U ⊓ KO k _, hUo.inter isOpen_KO, fun u hu h => ?_⟩
    have hu1 : u ∈ U := (Subgroup.mem_inf.1 hu).1
    have hv := valuation_gdet_of_mem_KO (Subgroup.mem_inf.1 hu).2
    have e : (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (h * u).val))) =
        fun g => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)) := by
      funext g
      rw [Units.val_mul, show g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (h.val * u.val)) = (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val)) * u.val by
        simp only [Matrix.mul_assoc], hU _ hu1]
    rw [pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ, e, gdet_mul, map_mul, apow_mul, hα _ hv, apow_of_valuation_eq_one hv]
    simp
  · have hdet := gdet_of_isBlockUpper hb h1 h2
    have e : (fun g : Matrix (Fin a') (Fin a') k => Ψ (g * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (b * h).val))) =
        fun g => (fun y => Ψ (y * (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * h.val))) (g * (blkDGL b dD h2).val) := by
      funext g
      simp only [Units.val_mul]
      rw [← Matrix.mul_assoc (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))), lowerProjection_blockUpper hb h2]
      simp only [Matrix.mul_assoc]
    rw [pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ, e,
      zetaUnr_mul_right hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ), gdet_mul, hdet]
    simp only [indFac, wt, gdet_blkDGL, map_mul, Units.val_mul, apow_mul, hS.quot, MonoidHom.div_apply,
      Units.val_div_eq_div_val]
    have hD : apow dD ((a' : ℂ) / 2) = apow dD (-(a : ℂ) / 2) * apow dD (((a + a' : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    rw [hD]
    have h3 := apow_ne_zero dD (((a + a' : ℕ) : ℂ) / 2)
    have h4 : (β dD : ℂ) ≠ 0 := Units.ne_zero _
    have h5 : (α dD : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
end PositivityTheory.ThK.SplitLoc.Unr
