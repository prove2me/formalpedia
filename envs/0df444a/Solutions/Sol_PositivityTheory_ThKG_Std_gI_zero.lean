-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.gI_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:22:55.938797+00:00
-- url     : https://prove2.me/submissions/e0b388ac-143a-4266-baf4-63c58e7f71fc

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_gI_small
import Theorems.Thm_PositivityTheory_ThKG_Std_gI_big
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
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hν : CondLE ϖ (c + 1) ν) (hν' : ¬ CondLE ϖ c ν) {y : k}
    (hy : valuation k (y * (ϖ : k) ^ (c + 1)) ≠ 1) : gI m ψ ν y = 0 := by
  by_cases h : valuation k (y * (ϖ : k) ^ (c + 1)) ≤ 1
  · refine gI_small hm hψ hϖ hν' ?_
    have h1 := le_uniformizer_iff.2 (lt_of_le_of_ne h hy)
    rw [← hϖ, pow_succ, ← mul_assoc, map_mul] at h1
    have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
    exact (mul_le_iff_le_one_left h0).1 h1
  · exact gI_big hm hψ hϖ (by omega) hν h
end PositivityTheory.ThKG.Std
