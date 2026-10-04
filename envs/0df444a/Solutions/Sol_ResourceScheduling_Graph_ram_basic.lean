-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_basic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:49.160985+00:00
-- url     : https://prove2.me/submissions/19ded5bf-1a7a-4a90-95ce-b6db8e5b9a3f

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (v : V) :
    StackImplements RAMRep (ramSkip (V := V)) id (fun _ => 1) ∧
    StackImplements RAMRep (ramZero v) (fun s => s.set v 0) (fun s => 3 * s.val v + 1) ∧
    StackImplements RAMRep (ramInc v) (fun s => s.set v (s.val v + 1)) (fun _ => 1) ∧
    StackImplements RAMRep (ramDec v) (fun s => s.set v (s.val v - 1)) (fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s l hr
    exact ⟨1, l, le_rfl, StackProg.Exec.act (fun _ _ => .keep) l, hr⟩
  · intro s l hr
    refine ⟨3 * (l (ramReg v)).length + 1, Function.update l (ramReg v) [], ?_,
      (stack_basic_macros (ramReg v) l).2.2, ?_⟩
    · simp [hr.1 v]
    · exact (ram_frames s l hr).1 v []
  · intro s l hr
    refine ⟨1, _, le_rfl, (stack_basic_macros (ramReg v) l).1 Letter.one, ?_⟩
    simpa [hr.1 v] using (ram_frames s l hr).1 v (Letter.one :: l (ramReg v))
  · intro s l hr
    refine ⟨1, _, le_rfl, (stack_basic_macros (ramReg v) l).2.1, ?_⟩
    simpa [hr.1 v] using (ram_frames s l hr).1 v (l (ramReg v)).tail

#print axioms solution
