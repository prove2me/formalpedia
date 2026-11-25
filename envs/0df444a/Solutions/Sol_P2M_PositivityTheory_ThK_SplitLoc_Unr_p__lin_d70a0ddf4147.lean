-- Prove2me | solution 1 for P2M_PositivityTheory_ThK_SplitLoc_Unr_p__lin_d70a0ddf4147
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:53.425166+00:00
-- url     : https://prove2.me/submissions/39185510-5410-4e7f-9c05-3fd751527178

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_add
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_comp_right
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
theorem _root_.solution (hS : HidaSetting a a' ϖ α β ν) (hν : IsUnram ν) : ∀ Ψ ∈ SB _, ∀ Ψ₁ ∈ SB _, ∀ c : ℂ,
    pUnr' a a' ϖ ν α (Ψ + c • Ψ₁) = pUnr' a a' ϖ ν α Ψ + c • pUnr' a a' ϖ ν α Ψ₁ := by
  intro Ψ hΨ Ψ₁ hΨ₁ c
  funext h
  have h2 : Ψ + c • Ψ₁ ∈ SB _ := (SB _).add_mem hΨ ((SB _).smul_mem c hΨ₁)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [pUnr'_eq hS hν h2, pUnr'_eq hS hν hΨ, pUnr'_eq hS hν hΨ₁, mul_left_comm c, ← mul_add,
    ← zetaUnr_add hS.unif hν _ _ (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ) (sb_comp_right (lowerProjection_mul_right_inverse h) hΨ₁)]
  rfl
end PositivityTheory.ThK.SplitLoc.Unr
