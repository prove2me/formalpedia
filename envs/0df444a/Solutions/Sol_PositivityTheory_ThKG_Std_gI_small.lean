-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.gI_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:29.815553+00:00
-- url     : https://prove2.me/submissions/50dda854-1ff1-4fcc-8f33-237149773e06

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Theorems.Thm_PositivityTheory_ThKG_Std_dl_of_ne
import Theorems.Thm_PositivityTheory_ThKG_Std_gI_unit
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_PositivityTheory_ThKG_Std_IsPsi_triv
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
theorem _root_.solution (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hν' : ¬ CondLE ϖ c ν) {y : k}
    (hy : valuation k (y * (ϖ : k) ^ c) ≤ 1) : gI m ψ ν y = 0 := by
  simp only [CondLE, not_forall] at hν'
  obtain ⟨u, ⟨hu, hu'⟩, hne⟩ := hν'
  have : gI m ψ ν (u * y) = gI m ψ ν y := by
    unfold gI
    congr 1
    funext r
    by_cases hr : valuation k r = 1
    · rw [show u * y * r = y * r + y * (u - 1) * r by ring, AddChar.map_add_eq_mul, hψ.triv (x := y * (u - 1) * r), mul_one]
      rw [map_mul, hr, mul_one, map_mul]
      refine le_trans ?_ hy
      rw [map_mul]
      exact mul_le_mul_right (by simpa using hu') _
    · simp [dl_of_ne hr]
  rw [gI_unit hm u hu] at this
  have h2 : ((ν u : ℂ) - 1) * gI m ψ ν y = 0 := by linear_combination this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 fun h => hne (Units.ext h))
end PositivityTheory.ThKG.Std
