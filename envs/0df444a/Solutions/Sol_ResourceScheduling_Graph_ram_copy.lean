-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_copy
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:50.471085+00:00
-- url     : https://prove2.me/submissions/da7c0778-61e1-41db-b3e9-09cc59c67328

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (src : RAMWire V) (v : V)
    (hd : src ≠ ramReg v) (ht : src ≠ ramTmp 0) (f : RAMState V → ℕ)
    (hf : ∀ s l, RAMRep s l → (l src).length = f s) :
    StackImplements RAMRep (ramAppend src v)
      (fun s => s.set v (f s + s.val v)) (fun s => 6 * f s + 3) ∧
    StackImplements RAMRep (ramAssign src v)
      (fun s => s.set v (f s)) (fun s => 3 * s.val v + 6 * f s + 5) := by
  have hdt : ramReg v ≠ (ramTmp 0 : RAMWire V) := by simp [ramReg, ramTmp]
  constructor
  · intro s l hr
    have he := stack_copy src (ramReg v) (ramTmp 0) hd ht hdt l (hr.2.2.2 0)
    refine ⟨6 * (l src).length + 3, _, ?_, he, ?_⟩
    · simp [hf s l hr]
    · simpa [hf s l hr, hr.1 v] using
        (ram_frames s l hr).1 v (l src ++ l (ramReg v))
  · intro s l hr
    let l' := Function.update l (ramReg v) []
    have hl : l' src = l src := by simp [l', hd]
    have he := stack_copy src (ramReg v) (ramTmp 0) hd ht hdt l'
      (by simpa [l', ramReg, ramTmp] using hr.2.2.2 0)
    have hout : Function.update l' (ramReg v) (l' src ++ l' (ramReg v)) =
        Function.update l (ramReg v) (l src) := by simp [l', hd]
    rw [hout] at he
    refine ⟨3 * (l (ramReg v)).length + 1 + 1 + (6 * (l' src).length + 3), _, ?_,
      ((stack_basic_macros (ramReg v) l).2.2).seq he, ?_⟩
    · simp only [hl, hf s l hr, hr.1 v]; omega
    · simpa [hf s l hr] using (ram_frames s l hr).1 v (l src)

#print axioms solution
