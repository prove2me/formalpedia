-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.p_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:42.610164+00:00
-- url     : https://prove2.me/submissions/d2eb9fee-7e1b-4e34-8cd1-54ca32ce6841

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_mul_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_stab
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_continuous_invT
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_pUnr_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gdet_blkAGL
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_gdet_of_isBlockUpper
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_inverse_transpose_block
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_upperProjection_inverse_transpose_right_inverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_add
import Theorems.Thm_GlobalTheory_SplitFlip_apow_inv
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_apow_neg
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_invT
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
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) (hβ : IsUnram β) :
    ∀ Φ ∈ SB _, pUnr a a' ϖ ν β Φ ∈ indSp a a' α β := by
  intro Φ hΦ
  refine ⟨?_, fun b h hb dA dD h1 h2 => ?_⟩
  · obtain ⟨U, hUo, hU⟩ := exists_stab hΦ
    refine ⟨U.comap invT ⊓ KO k _, (hUo.preimage continuous_invT).inter isOpen_KO, fun u hu h => ?_⟩
    have hu1 : invT u ∈ U := Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).1
    have hu2 : u ∈ KO k _ := (Subgroup.mem_inf.1 hu).2
    have hv := valuation_gdet_of_mem_KO hu2
    have e : (fun g : Matrix (Fin a) (Fin a) k => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT (h * u)).val))) =
        fun g => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)) := by
      funext g
      rw [map_mul, Units.val_mul, show g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * ((invT h).val * (invT u).val)) =
        (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val)) * (invT u).val by simp only [Matrix.mul_assoc], hU _ hu1]
    rw [pUnr_eq, pUnr_eq, e, gdet_mul, map_mul, apow_mul, hβ _ hv, apow_of_valuation_eq_one hv]
    simp
  · have hdet := gdet_of_isBlockUpper hb h1 h2
    have e : (fun g : Matrix (Fin a) (Fin a) k => Φ (g * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT (b * h)).val))) =
        fun g => (fun y => Φ (y * (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')) * (invT h).val))) (g * (invT (blkAGL b dA h1)).val) := by
      funext g
      simp only [map_mul, Units.val_mul]
      rw [← Matrix.mul_assoc (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))), upperProjection_inverse_transpose_block hb h1]
      simp only [Matrix.mul_assoc]
    rw [pUnr_eq, pUnr_eq, e, zetaUnr_mul_right hS.unif hν _ _ (sb_comp_right (upperProjection_inverse_transpose_right_inverse h) hΦ), gdet_mul, hdet]
    simp only [indFac, wt, gdet_invT, gdet_blkAGL, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      apow_mul, apow_inv, hS.quot, MonoidHom.div_apply, Units.val_div_eq_div_val]
    have hA : apow dA ((a' : ℂ) / 2) = apow dA (-(a : ℂ) / 2) * apow dA (((a + a' : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    rw [hA, apow_neg]
    have h3 := apow_ne_zero dA (((a + a' : ℕ) : ℂ) / 2)
    have h4 : (β dA : ℂ) ≠ 0 := Units.ne_zero _
    have h5 : (α dA : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
end PositivityTheory.ThK.SplitLoc.Unr
