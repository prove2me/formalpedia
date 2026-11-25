-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.gI_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:52.406803+00:00
-- url     : https://prove2.me/submissions/fb9efe07-1f15-45f1-9f72-3f0ebf970fe6

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_mul_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_int_scale
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
theorem _root_.solution (hm : IsVol m) (u : kˣ) (hu : valuation k (u : k) = 1) (y : k) : gI m ψ ν (u * y) = ν u * gI m ψ ν y := by
  rw [gI, gI, ← int_scale hm u hu (fun r => dl ν r * ψ (y * r)), ← integral_const_mul]
  congr 1
  funext r
  rw [dl_mul_unit hu, dl_unit u hu, show y * (u * r) = u * y * r by ring]
  simp [← mul_assoc]
end PositivityTheory.ThKG.Std
