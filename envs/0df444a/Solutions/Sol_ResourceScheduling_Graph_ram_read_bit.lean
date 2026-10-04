-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_read_bit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:38:52.922593+00:00
-- url     : https://prove2.me/submissions/ae378cde-1300-48a6-b9ce-d18cc35c88a5

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_CookPvsNP_stack_lookup
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i dst : V) :
    StackImplements RAMRep (ramReadBit i dst)
      (fun s => s.set dst (if s.word.getD (s.val i) Letter.sep = Letter.one then 1 else 0))
      (fun s => 9 * s.word.length + 9 * s.val i + 3 * s.val dst + 17) := by
  intro s l hr
  let a := s.word.getD (s.val i) Letter.sep
  let l1 := Function.update l (ramTmp 0) [a]
  let l2 := Function.update l1 (ramReg dst) []
  let w := if a = Letter.one then [Letter.one] else []
  obtain ⟨n, hn, he⟩ := stack_lookup (ramLookupPorts i) Letter.sep l
    (hr.2.2.2 0) (hr.2.2.2 1) (hr.2.2.2 2) (hr.2.2.2 3)
  change n ≤ 9 * (l ramInput).length + 9 * (l (ramReg i)).length + 13 at hn
  change (lookupProg (ramLookupPorts i) Letter.sep).Exec l
    (Function.update l (ramTmp 0) [(l ramInput).getD (l (ramReg i)).length Letter.sep]) n at he
  rw [hr.2.1, hr.1 i] at he hn
  have hzero := (stack_basic_macros (ramReg dst) l1).2.2
  let act := fun (h : RAMWire V → Option Letter) k =>
    if k = ramTmp 0 then StackAct.pop else
    if k = ramReg dst ∧ h (ramTmp 0) = some Letter.one then .push Letter.one else .keep
  have hout : StackProg.applyAct act l2 = Function.update l (ramReg dst) w := by
    funext k
    by_cases hk : k = ramTmp 0
    · subst k
      simpa [StackProg.applyAct, act, l2, l1, ramTmp, ramReg, StackAct.apply]
        using hr.2.2.2 0
    by_cases hd : k = ramReg dst
    · subst k
      by_cases ha : a = Letter.one <;>
        simp [StackProg.applyAct, act, l2, l1, ramTmp, ramReg, StackAct.apply, w, ha]
    · simp [StackProg.applyAct, act, l2, l1, StackAct.apply, hk, hd]
  have hend := StackProg.Exec.act act l2
  rw [hout] at hend
  refine ⟨n + 1 + (3 * (l1 (ramReg dst)).length + 1 + 1 + 1), _, ?_,
    he.seq (hzero.seq hend), ?_⟩
  · have hd : (l1 (ramReg dst)).length = s.val dst := by
      simpa [l1, ramReg, ramTmp] using hr.1 dst
    rw [hd]; dsimp only; omega
  · have hw : w.length = if a = Letter.one then 1 else 0 := by dsimp [w]; split <;> rfl
    simpa only [hw] using (ram_frames s l hr).1 dst w

#print axioms solution
