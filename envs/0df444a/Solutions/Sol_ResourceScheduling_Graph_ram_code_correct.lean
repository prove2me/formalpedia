-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_code_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:23:35.398545+00:00
-- url     : https://prove2.me/submissions/2baab523-63b1-4dfa-be05-64d00878035d

import Definitions.Def_ResourceScheduling_Graph_RAMCode
import Theorems.Thm_ResourceScheduling_Graph_ram_basic
import Theorems.Thm_ResourceScheduling_Graph_ram_copy
import Theorems.Thm_ResourceScheduling_Graph_ram_sub
import Theorems.Thm_ResourceScheduling_Graph_ram_mul
import Theorems.Thm_ResourceScheduling_Graph_ram_read_bit
import Theorems.Thm_ResourceScheduling_Graph_ram_emit
import Theorems.Thm_ResourceScheduling_Graph_ram_parse
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint
import Theorems.Thm_CookPvsNP_stack_specification_seq
import Theorems.Thm_CookPvsNP_stack_specification_branch
import Theorems.Thm_CookPvsNP_stack_specification_loop

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (p : RAMCode V) (hp : p.Valid) :
    StackImplements RAMRep p.code p.eval p.cost := by
  induction p with
  | skip =>
    intro s l hr
    exact ⟨1, l, le_rfl, StackProg.Exec.act (fun _ _ => .keep) l, hr⟩
  | zero v => exact (ram_basic v).2.1
  | inc v => exact (ram_basic v).2.2.1
  | dec v => exact (ram_basic v).2.2.2
  | copy i v h =>
    exact (ram_copy (ramReg i) v (by simpa [ramReg] using h)
      (by simp [ramReg, ramTmp]) (fun s => s.val i) (fun _ _ hr => hr.1 i)).2
  | add i v h =>
    exact (ram_copy (ramReg i) v (by simpa [ramReg] using h)
      (by simp [ramReg, ramTmp]) (fun s => s.val i) (fun _ _ hr => hr.1 i)).1
  | length v =>
    exact (ram_copy ramInput v (by simp [ramInput, ramReg])
      (by simp [ramInput, ramTmp]) (fun s => s.word.length) (fun _ _ hr => congrArg List.length hr.2.1)).2
  | sub i j v => exact ram_sub i j v
  | mul i j v h => exact ram_mul i j v h
  | bit i v => exact ram_read_bit i v
  | emit v => exact ram_emit v
  | parse t good h => exact ram_parse t good h
  | seq p q ihp ihq =>
    exact stack_specification_seq RAMRep p.code q.code p.eval q.eval p.cost q.cost
      (ihp hp.1) (ihq hp.2)
  | branch v p q ihp ihq =>
    simpa [RAMCode.code, RAMCode.eval, RAMCode.cost] using
      stack_specification_branch RAMRep p.code q.code
        (fun h => (h (ramReg v)).isSome) (fun s => decide (0 < s.val v))
        p.eval q.eval p.cost q.cost (ihp hp.1) (ihq hp.2)
        (fun s l hr => (ram_frames s l hr).2.2.2 v)
  | loop v p ih =>
    have hb := stack_specification_seq RAMRep (ramDec v) p.code
      (fun s => s.set v (s.val v - 1)) p.eval (fun _ => 1) p.cost
      (ram_basic v).2.2.2 (ih hp.1)
    exact stack_specification_loop RAMRep ((ramDec v).seq p.code)
      (fun h => (h (ramReg v)).isSome) (fun s => p.eval (s.set v (s.val v - 1)))
      (fun s => 1 + 1 + p.cost (s.set v (s.val v - 1))) (fun s => s.val v) hb
      (fun s l hr => (ram_frames s l hr).2.2.2 v) (by
        intro s hs
        rw [ram_footprint p v hp.2]
        simp only [RAMState.set, Function.update_self]
        omega)

#print axioms solution
