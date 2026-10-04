-- Prove2me | solution 1 for ResourceScheduling.Graph.program_cost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:56.050425+00:00
-- url     : https://prove2.me/submissions/ac0f8f23-3db2-4f37-a154-c5322b873953

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Theorems.Thm_ResourceScheduling_Graph_program_run
import Theorems.Thm_ResourceScheduling_Graph_ram_budget
import Theorems.Thm_ResourceScheduling_Graph_word_program_correct
import Theorems.Thm_ResourceScheduling_Graph_reduceWord_correct
import Theorems.Thm_ResourceScheduling_Graph_source_budget

set_option autoImplicit false
set_option maxRecDepth 4096
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution : ∃ k, ∀ w : List Letter,
    program.cost ⟨fun _ => 0, w, []⟩ + 3 * (wordProgram w).length + 2 ≤ w.length ^ k + k := by
  obtain ⟨k,hk⟩ := source_budget program.weight program.degree (by decide)
  refine ⟨k, ?_⟩
  intro w
  let B := 100 * (w.length + 1)^2
  let s : RAMState GraphReg := ⟨fun _ => 0, w, []⟩
  have hs : RAMBound B s := by
    constructor
    · intro v; exact Nat.zero_le _
    · change w.length ≤ B; dsimp [B]; nlinarith
  have hb := (program_run B w.length s hs le_rfl (by dsimp [B]; nlinarith)).1.1
  have hc := ram_budget program B s hb
  have ho : (wordProgram w).length ≤ 5 * w.length^2 + 8 := by
    rw [word_program_correct]
    exact (reduceWord_correct w).2
  exact hk w.length (program.cost s) (wordProgram w).length hc ho

#print axioms solution
