-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:35.777792+00:00
-- url     : https://prove2.me/submissions/4dd5a34a-d956-4566-8d17-a70d62851ba0

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_wt_of_mem
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_finsum_conv_shift
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_of_shift
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_conv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) (g₁ : GL (Fin n) k) :
    zetaUnr n d ϖ ν (fun x => φ (g₁.val * x)) = (wt d ν g₁)⁻¹ * zetaUnr n d ϖ ν φ := by
  rw [zetaUnr_eq_conv, zetaUnr_eq_conv, zCoeff_of_shift hϖ hν d hφ (sb_mul_left hφ g₁) (Jm_mul_left φ g₁),
    finsum_conv_shift, wt_of_mem hϖ hν d (m := ord k (gdet g₁)) rfl]
end PositivityTheory.ThK.SplitLoc.Unr
