-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.IsPsi.ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:14.200875+00:00
-- url     : https://prove2.me/submissions/3308d0f2-18a7-4410-a458-d8731e6126ef

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
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
omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThKG.Std
namespace IsPsi
theorem _root_.solution {ψ : AddChar k ℂ} (h : IsPsi ψ) : ψ ≠ 1 := by
  rintro rfl
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  have := (h.cond (ϖ⁻¹ : kˣ)).1 fun _ _ => rfl
  have h2 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simp))] at this
  exact absurd this (not_le.2 h2)
end IsPsi
end PositivityTheory.ThKG.Std
