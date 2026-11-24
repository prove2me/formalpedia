-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.dl_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:32.430715+00:00
-- url     : https://prove2.me/submissions/e877a08b-1790-4167-aa90-98e89f1a94e2

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_unit
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_of_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_exists_unit
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
theorem _root_.solution {x : k} (hx : valuation k x = 1) (y : k) : dl ν (x * y) = dl ν x * dl ν y := by
  by_cases hy : valuation k y = 1
  · obtain ⟨u, rfl⟩ := exists_unit hx
    obtain ⟨w, rfl⟩ := exists_unit hy
    rw [← Units.val_mul, dl_unit _ (by simp [hx, hy]), dl_unit _ hx, dl_unit _ hy, map_mul, mul_inv, Units.val_mul]
  · rw [dl_of_ne hy, mul_zero, dl_of_ne (by rwa [map_mul, hx, one_mul])]
end PositivityTheory.ThKG.Std
