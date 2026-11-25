-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:37.181151+00:00
-- url     : https://prove2.me/submissions/9096d433-814e-4604-94a4-d8a7cd3af413

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_integrableOn_dShell
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_add
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_finite
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_conv
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
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (n d : ℕ)
    {φ ψ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (hψ : ψ ∈ SB _) (c : ℂ) :
    zetaUnr n d ϖ ν (fun x => φ x + c * ψ x) = zetaUnr n d ϖ ν φ + c * zetaUnr n d ϖ ν ψ := by
  have hs : (fun x => φ x + c * ψ x) ∈ SB (Matrix (Fin n) (Fin n) k) :=
    (SB _).add_mem hφ ((SB _).smul_mem c hψ)
  have hz : zCoeff n d ϖ ν (fun x => φ x + c * ψ x) =
      fun m => zCoeff n d ϖ ν φ m + c * zCoeff n d ϖ ν ψ m := by
    funext m
    rw [zCoeff_eq hϖ hν d hs, zCoeff_eq hϖ hν d hφ, zCoeff_eq hϖ hν d hψ]
    unfold Jm
    rw [integral_add (integrableOn_dShell hφ m) ((integrableOn_dShell hψ m).const_mul c), integral_const_mul]
    ring
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, zetaUnr_eq_conv, hz]
  simp only [conv_add]
  rw [finsum_add_distrib (conv_finite hϖ hν n d hφ)
    ((conv_finite hϖ hν n d hψ).subset fun m hm => right_ne_zero_of_mul hm), ← smul_eq_mul c, smul_finsum]
  rfl
end PositivityTheory.ThK.SplitLoc.Unr
