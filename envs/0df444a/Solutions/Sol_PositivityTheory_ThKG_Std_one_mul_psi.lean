-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.one_mul_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:59.551059+00:00
-- url     : https://prove2.me/submissions/97b221be-47ed-43b2-a180-31138f48ca63

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_triv
import Theorems.Thm_PositivityTheory_ThKG_Std_val_dot
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] [DecidableEq κ]
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {ψ : AddChar k ℂ} (h : IsPsi ψ) {x y : κ → k} (hy : ∀ p, valuation k (y p) ≤ 1) :
    ψ (x ⬝ᵥ y) * one κ x = one κ x := by
  by_cases h0 : one κ x = 0
  · rw [h0, mul_zero]
  · rw [h.triv (val_dot (fun p => by simpa using ind_ne (Finset.prod_ne_zero_iff.1 h0 p (Finset.mem_univ _))) hy), one_mul]
end PositivityTheory.ThKG.Std
