-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.conv_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:31.133961+00:00
-- url     : https://prove2.me/submissions/b3506159-1793-4529-8ea8-25c8199e7d81

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_Jm_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_exists_normal
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_shift
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_cst_ne_zero
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_sb_mul_left
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zCoeff_of_shift
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_finite_normal

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
    {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    (Function.support (conv (invL n d ϖ ν) n (zCoeff n d ϖ ν φ))).Finite := by
  obtain ⟨N, M, hs, hp⟩ := exists_normal hϖ hφ
  have h₀ := sb_mul_left hφ (scal n (ϖ ^ N)⁻¹)
  have hf := conv_finite_normal hϖ hν n d h₀ hs M hp
  rw [zCoeff_of_shift hϖ hν d hφ h₀ (Jm_mul_left φ _)] at hf
  refine (hf.image (· + ord k (gdet (scal n (ϖ ^ N)⁻¹)))).subset fun m hm => ?_
  refine ⟨m - ord k (gdet (scal n (ϖ ^ N)⁻¹)), ?_, sub_add_cancel _ _⟩
  rw [Function.mem_support, conv_shift, sub_add_cancel]
  exact mul_ne_zero (inv_ne_zero (zpow_ne_zero _ (cst_ne_zero d ϖ ν))) hm
end PositivityTheory.ThK.SplitLoc.Unr
