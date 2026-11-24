-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.dl_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.796269+00:00
-- url     : https://prove2.me/submissions/379599f0-777a-4591-8b32-20b8da9c8923

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_of_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_exists_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_mul_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_val_pow_lt
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
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (x : k) {t : k} (ht : valuation k t ≤ valuation k ((ϖ : k) ^ c)) :
    dl ν (x + t) = dl ν x := by
  have hl := lt_of_le_of_lt ht (val_pow_lt hϖ hc)
  by_cases hx : valuation k x = 1
  · obtain ⟨u, rfl⟩ := exists_unit hx
    have h1 : valuation k ((u : k)⁻¹ * t) ≤ valuation k ((ϖ : k) ^ c) := by rwa [map_mul, map_inv₀, hx, inv_one, one_mul]
    have h2 : valuation k (1 + (u : k)⁻¹ * t) = 1 := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt hϖ hc))
    obtain ⟨w, hw⟩ := exists_unit h2
    have : (u : k) + t = u * w := by rw [hw, mul_add, mul_one, mul_inv_cancel_left₀ u.ne_zero]
    rw [this, dl_mul_unit hx, dl_unit w (hw ▸ h2), hν w ⟨hw ▸ h2, by rw [hw]; simpa using h1⟩]
    simp
  · rw [dl_of_ne hx, dl_of_ne]
    intro h
    apply hx
    have := (valuation k).map_sub_eq_of_lt_left (x := x + t) (y := t) (h ▸ hl)
    rwa [add_sub_cancel_right, h] at this
end PositivityTheory.ThKG.Std
