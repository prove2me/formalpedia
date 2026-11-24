-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.split_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:47.17098+00:00
-- url     : https://prove2.me/submissions/e2458490-f784-4f9a-bd1a-f3eb2e8df954

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
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
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution {e : Fin n → Fin d} (P : Finset (Fin n × Fin d)) (Y : Matrix (Fin n) (Fin d) k) (hY : ∀ p ∈ P, Y p.1 p.2 = 0)
    (Z : Fin n × Fin d → k) : (∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) ((tm (cut P Z) + Y) p.1 p.2)) * wt P Z =
      (∏ p : Fin n × Fin d, if p ∈ P then 1 else ind (rad ϖ c e p.2) (Y p.1 p.2)) *
        ∏ p : Fin n × Fin d, (if p ∈ P then ind (rad ϖ c e p.2) (Z p) else ind 1 (Z p)) := by
  rw [wt, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : p ∈ P
  · simp [tm, cut, hp, hY p hp]
  · simp [tm, cut, hp]
end PositivityTheory.ThKG.Std
