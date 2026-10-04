-- Prove2me | solution 1 for ResourceScheduling.Graph.reduceWord_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:48.801856+00:00
-- url     : https://prove2.me/submissions/a258182c-2334-418d-ade9-9e4fc9210e75

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_ResourceScheduling_Graph_program_run
import Theorems.Thm_ResourceScheduling_Graph_program_cost
import Theorems.Thm_ResourceScheduling_Graph_program_valid
import Theorems.Thm_ResourceScheduling_Graph_ram_code_correct
import Theorems.Thm_ResourceScheduling_Graph_word_program_correct
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_program_polytime

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph GraphProgram

theorem solution : PolyTimeComputable reduceWord := by
  let finish : StackProg (RAMWire GraphReg) Letter :=
    transferProg ramOutput (fun j => decide (j = ramTmp 0))
  let p := program.code.seq finish
  obtain ⟨k,hk⟩ := program_cost
  apply stack_program_polytime p ramInput (ramTmp 0) reduceWord k
  intro w
  let s : RAMState GraphReg := ⟨fun _ => 0, w, []⟩
  let l := fun j : RAMWire GraphReg => if j = ramInput then w else []
  have hrep : RAMRep s l := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v; simp [l, s, ramReg, ramInput]
    · simp [l, s]
    · simp [l, s, ramOutput, ramInput]
    · intro i; simp [l, ramTmp, ramInput]
  obtain ⟨a,l',ha,hex,hrep'⟩ := ram_code_correct program program_valid s l hrep
  let B := 100 * (w.length + 1)^2
  have hs : RAMBound B s := by
    refine ⟨fun _ => Nat.zero_le _, ?_⟩
    change w.length ≤ B; dsimp [B]; nlinarith
  have hout : (program.eval s).out = (wordProgram w).reverse := by
    simpa only [s, List.append_nil] using
      (program_run B w.length s hs le_rfl (by dsimp [B]; nlinarith)).2
  have ho : l' ramOutput = (wordProgram w).reverse := hrep'.2.2.1.trans hout
  have hf := stack_transfer ramOutput (fun j : RAMWire GraphReg => decide (j = ramTmp 0)) l'
  refine ⟨transferStore ramOutput (fun j => decide (j = ramTmp 0)) l',
    a + 1 + (3 * (l' ramOutput).length + 1), ?_, hex.seq hf, ?_⟩
  · have hb := hk w
    rw [ho, List.length_reverse]
    dsimp [s] at ha
    omega
  · simp [transferStore, show (ramTmp 0 : RAMWire GraphReg) ≠ ramOutput from by decide,
      ho, hrep'.2.2.2 0, word_program_correct]

#print axioms solution
