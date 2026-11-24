-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:39.806816+00:00
-- url     : https://prove2.me/submissions/6b6952c4-5b57-41c1-bb79-adf52f9d28ce

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finsum_conv_shift
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
theorem _root_.solution (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (c : ℂ) :
    zetaUnr n d ϖ ν (fun x => c * φ x) = c * zetaUnr n d ϖ ν φ := by
  have hz : zCoeff n d ϖ ν (fun x => c * φ x) = fun m => c * zCoeff n d ϖ ν φ (m + 0) := by
    funext m
    rw [add_zero, zCoeff, zCoeff, ← smul_eq_mul c, smul_finsum]
    refine finsum_congr fun a => ?_
    simp only [shell, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, hz, finsum_conv_shift]
end PositivityTheory.ThK.SplitLoc.Unr
