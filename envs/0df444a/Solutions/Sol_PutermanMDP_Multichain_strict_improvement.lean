-- Prove2me | solution 1 for PutermanMDP.Multichain.strict_improvement
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:25:42.006993+00:00
-- url     : https://prove2.me/submissions/19a8006e-0253-455c-8974-756a61fc2dc3

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses Filter
open scoped Topology
open PutermanMDP.Multichain

theorem solution : ¬ (∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]
    (M : StationaryMDP S A) (δ d : Rule M) (h : ImprovementCondition M δ d),
    StrictNearOneImprovement M δ d) := by
  intro H
  let M : StationaryMDP PUnit PUnit :=
    { admissible := fun _ => {PUnit.unit}
      admissible_nonempty := fun _ => ⟨PUnit.unit, by simp⟩
      reward := fun _ _ => 0
      trans := fun _ _ _ => 1
      trans_nonneg := fun _ _ _ => by norm_num
      trans_sum := fun _ _ => by simp }
  let d : Rule M := ⟨fun _ => PUnit.unit, fun s => by simp [M]⟩
  have hc : ImprovementCondition M d d := by
    intro s hne
    exact absurd rfl hne
  obtain ⟨s, hs⟩ := H M d d hc
  simp only [sub_self, EReal.coe_zero] at hs
  rw [Filter.liminf_const] at hs
  exact lt_irrefl _ hs
