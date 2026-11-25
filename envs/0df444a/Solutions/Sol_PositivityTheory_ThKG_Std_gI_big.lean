-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.gI_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:34.094952+00:00
-- url     : https://prove2.me/submissions/d078e0ee-9e6b-494c-8f4b-352a6d89b769

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_add
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_ex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) {y : k}
    (hy : ¬ valuation k (y * (ϖ : k) ^ c) ≤ 1) : gI m ψ ν y = 0 := by
  haveI := hm.haar
  obtain ⟨s, hs, hne⟩ := hψ.ex hy
  have ht : valuation k ((ϖ : k) ^ c * s) ≤ valuation k ((ϖ : k) ^ c) := by rw [map_mul]; exact mul_le_of_le_one_right' hs
  have : gI m ψ ν y = ψ (y * ϖ ^ c * s) * gI m ψ ν y := by
    conv_lhs => rw [gI, ← integral_add_right_eq_self _ ((ϖ : k) ^ c * s)]
    rw [gI, ← integral_const_mul]
    congr 1
    funext r
    rw [dl_add hϖ hc hν r ht, mul_add, AddChar.map_add_eq_mul, mul_assoc y]
    ring
  have h2 : (ψ (y * ϖ ^ c * s) - 1) * gI m ψ ν y = 0 := by linear_combination -this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
end PositivityTheory.ThKG.Std
