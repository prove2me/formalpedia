-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_mul
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:55:55.790242+00:00
-- url     : https://prove2.me/submissions/322be5f2-76ac-4fe1-88d3-eadac7d8b789

import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i j dst : V) (h : j ≠ dst) :
    StackImplements RAMRep (ramMul i j dst h)
      (fun s => s.set dst (s.val i * s.val j))
      (fun s => (6 * s.val j + 13) * s.val i + 3 * s.val dst + 7) := by
  intro s l hr
  let x := l (ramReg i)
  let y := l (ramReg j)
  let l1 := Function.update l (ramTmp 0) x
  let l2 := Function.update l1 (ramReg dst) []
  have he1 := stack_copy (ramReg i) (ramTmp 0) (ramTmp 1)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l (hr.2.2.2 1)
  simp only [hr.2.2.2 0, List.append_nil] at he1
  have he2 := (stack_basic_macros (ramReg dst) l1).2.2
  have he3 := stack_repeat_copy (ramMulPorts j dst h) l2
    (by simpa [ramMulPorts, l2, l1, ramReg, ramTmp] using hr.2.2.2 1)
  change (repeatCopyProg (ramMulPorts j dst h)).Exec l2
    (Function.update (Function.update l2 (ramTmp 0) []) (ramReg dst)
      ((List.replicate (l2 (ramTmp 0)).length (l2 (ramReg j))).flatten ++ l2 (ramReg dst)))
    ((6 * (l2 (ramReg j)).length + 7) * (l2 (ramTmp 0)).length + 1) at he3
  have hf : Function.update (Function.update l2 (ramTmp 0) []) (ramReg dst)
      ((List.replicate (l2 (ramTmp 0)).length (l2 (ramReg j))).flatten ++ l2 (ramReg dst)) =
      Function.update l (ramReg dst) (List.replicate x.length y).flatten := by
    funext k
    by_cases hd : k = ramReg dst
    · subst k; simp [l2, l1, x, y, ramReg, ramTmp, h]
    by_cases ht : k = ramTmp 0
    · subst k
      simpa [l2, l1, ramReg, ramTmp] using (hr.2.2.2 0).symm
    · simp [l2, l1, hd, ht]
  rw [hf] at he3
  refine ⟨_, _, ?_, he1.seq (he2.seq he3), ?_⟩
  · have hy : (l2 (ramReg j)).length = s.val j := by
      simpa [l2, l1, ramReg, ramTmp, h] using hr.1 j
    have hx : (l2 (ramTmp 0)).length = s.val i := by
      simpa [l2, l1, x, ramReg, ramTmp] using hr.1 i
    have hd : (l1 (ramReg dst)).length = s.val dst := by
      simpa [l1, ramReg, ramTmp] using hr.1 dst
    rw [hy, hx, hd, hr.1 i]; dsimp only; nlinarith
  · simpa [List.length_flatten, x, y, hr.1 i, hr.1 j] using
      (ram_frames s l hr).1 dst (List.replicate x.length y).flatten

#print axioms solution
