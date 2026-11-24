-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.prod_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:48.179799+00:00
-- url     : https://prove2.me/submissions/8ec4a73c-b2c1-46d2-940c-4e977444b5b8

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_mid
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_off
import Theorems.Thm_PositivityTheory_ThKG_Std_ind_zero
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
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hr : Function.Injective jr) (hc : Function.Injective jc) {e : Fin n → Fin d} {e₁ : Fin n₁ → Fin d₁}
    (he : ∀ j, jc j ∈ Set.range e ↔ j ∈ Set.range e₁) {P : Finset (Fin n × Fin d)} (hP : ∀ i j, (jr i, jc j) ∉ P)
    (y : Matrix (Fin n₁) (Fin d₁) k) :
    ∏ p : Fin n × Fin d, (if p ∈ P then 1 else ind (rad ϖ c e p.2) (ext jr jc y p.1 p.2)) =
      ∏ p : Fin n₁ × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2) := by
  refine (Fintype.prod_of_injective (Prod.map jr jc) (hr.prodMap hc) _ _ (fun p hp => ?_) fun p => ?_).symm
  · rw [ext_off, ind_zero, ite_self]
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, j, hj⟩ := h
    exact hp ⟨(i, j), Prod.ext hi.symm hj.symm⟩
  · simp only [Prod.map, if_neg (hP _ _), ext_mid hr hc, rad, he]
end PositivityTheory.ThKG.Std
