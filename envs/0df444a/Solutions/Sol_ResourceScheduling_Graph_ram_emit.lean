-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_emit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:51.845317+00:00
-- url     : https://prove2.me/submissions/07668816-ab32-4efe-8e50-045f77f4f703

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_ResourceScheduling_Graph_stack_emit

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) :
    StackImplements RAMRep (ramEmit v)
      (fun s => { s with out := Letter.sep :: (List.replicate (s.val v) Letter.one ++ s.out) })
      (fun s => 9 * s.val v + 7) := by
  intro s l hr
  have he := stack_emit (ramEmitPorts v) l (hr.2.2.2 0) (hr.2.2.2 1)
  change (ramEmit v).Exec l (Function.update l ramOutput
    (Letter.sep :: (List.replicate (l (ramReg v)).length Letter.one ++ l ramOutput)))
    (9 * (l (ramReg v)).length + 7) at he
  rw [hr.1 v, hr.2.2.1] at he
  refine ⟨9 * s.val v + 7, _, le_rfl, he, ?_⟩
  exact (ram_frames s l hr).2.2.1 _

#print axioms solution
