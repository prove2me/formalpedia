-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.prod_vol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:51.947903+00:00
-- url     : https://prove2.me/submissions/d5771c69-0d5d-4bb4-b14d-83d599cd5533

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind_one
import Theorems.Thm_PositivityTheory_ThKG_Std_int_ind_pow
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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {P : Finset (Fin n × Fin d)} {r : ℕ}
    (g : Fin r → Fin n × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e) :
    ∏ p : Fin n × Fin d, ∫ x, (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) ∂m = (((resCard k : ℂ) ^ c)⁻¹) ^ r := by
  rw [← Fin.prod_const]
  refine (Fintype.prod_of_injective g hg _ _ (fun p hp => ?_) fun p => ?_).symm
  · by_cases h1 : p ∈ P
    · have h2 : p.2 ∈ Set.range e := by by_contra h2; exact hp ((h p).2 ⟨h1, h2⟩)
      simp only [if_pos h1, rad, if_pos h2, int_ind_one hm]
    · simp only [if_neg h1, int_ind_one hm]
  · obtain ⟨h1, h2⟩ := (h _).1 ⟨p, rfl⟩
    simp only [if_pos h1, rad, if_neg h2, int_ind_pow hm hϖ]
end PositivityTheory.ThKG.Std
