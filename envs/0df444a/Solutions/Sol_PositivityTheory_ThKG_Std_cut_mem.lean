-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.cut_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:35.094121+00:00
-- url     : https://prove2.me/submissions/e0d07324-fa6d-401c-88e5-1a5bc0021fe0

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_lc_wt
import Theorems.Thm_PositivityTheory_ThKG_Std_continuous_cut
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {P : Finset κ} {Φ : (κ → k) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.SB (κ → k)) :
    (fun Z => Φ (cut P Z) * wt P Z) ∈ GlobalTheory.WeilM.SB (κ → k) := by
  refine ⟨(hΦ.1.comp_continuous (continuous_cut P)).mul (lc_wt P), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi (s := fun p => if p ∈ P then (fun x : κ → k => x p) '' tsupport Φ else
    {x : k | valuation k x ≤ valuation k 1}) fun p => ?_) fun x hx => ?_
  · split_ifs
    · exact IsCompact.image hΦ.2 (continuous_apply p)
    · exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hx fun p _ => ?_
    by_cases hp : p ∈ P
    · simp only [if_pos hp]; exact ⟨cut P x, subset_tsupport _ h1, by simp [cut, hp]⟩
    · simp only [if_neg hp]
      have := Finset.prod_ne_zero_iff.1 h2 p (Finset.mem_univ _)
      rw [if_neg hp] at this
      exact ind_ne this
end PositivityTheory.ThKG.Std
