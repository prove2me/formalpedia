-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.lc_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:58.391261+00:00
-- url     : https://prove2.me/submissions/958ba3b7-c153-43a5-805a-ebfa0d109aa9

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_add
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_PositivityTheory_ThKG_Std_isClopen_ball
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
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) : IsLocallyConstant (dl ν) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : {t : k | valuation k t ≤ valuation k ((ϖ : k) ^ c)} ∈ 𝓝 (0 : k) :=
    (isClopen_ball (pow_ne_zero _ ϖ.ne_zero)).2.mem_nhds (by simp)
  have h2 : Filter.Tendsto (fun y => y - x) (𝓝 x) (𝓝 0) := by
    have : Continuous fun y : k => y - x := by fun_prop
    simpa using this.tendsto x
  filter_upwards [h2 h] with y hy
  rw [← dl_add hϖ hc hν x hy, add_sub_cancel]
end PositivityTheory.ThKG.Std
