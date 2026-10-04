-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_sub
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:55:55.12915+00:00
-- url     : https://prove2.me/submissions/6ab3321c-bca4-44ab-8096-558306abb8f5

import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
import Theorems.Thm_ResourceScheduling_Graph_ram_frames
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_consume
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (i j dst : V) :
    StackImplements RAMRep (ramSub i j dst)
      (fun s => s.set dst (s.val i - s.val j))
      (fun s => 9 * s.val i + 9 * s.val j + 3 * s.val dst + 13) := by
  intro s l hr
  let x := l (ramReg i)
  let y := l (ramReg j)
  let l1 := Function.update l (ramTmp 0) x
  let l2 := Function.update l1 (ramTmp 1) y
  let l3 := Function.update l (ramTmp 0) (x.drop y.length)
  let l4 := Function.update l3 (ramReg dst) []
  have he1 := stack_copy (ramReg i) (ramTmp 0) (ramTmp 2)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l (hr.2.2.2 2)
  simp only [hr.2.2.2 0, List.append_nil] at he1
  have he2 := stack_copy (ramReg j) (ramTmp 1) (ramTmp 2)
    (by simp [ramReg, ramTmp]) (by simp [ramReg, ramTmp]) (by simp [ramTmp]) l1
    (by simpa [l1, ramTmp] using hr.2.2.2 2)
  have hy : l1 (ramReg j) = y := by simp [l1, y, ramReg, ramTmp]
  have he0 : l1 (ramTmp 1) = [] := by simpa [l1, ramTmp] using hr.2.2.2 1
  simp only [hy, he0, List.append_nil] at he2
  have he3 := stack_consume (ramTmp 1) (fun k => decide (k = ramTmp 0)) l2
  have hf3 : consumeStore (ramTmp 1) (fun k => decide (k = ramTmp 0)) l2 = l3 := by
    funext k
    by_cases h0 : k = ramTmp 0
    · subst k; simp [consumeStore, l2, l1, l3, ramTmp]
    by_cases h1 : k = ramTmp 1
    · subst k; simpa [consumeStore, l3, ramTmp] using hr.2.2.2 1
    · simp [consumeStore, l2, l1, l3, h0, h1]
  rw [hf3] at he3
  have he4 := (stack_basic_macros (ramReg dst) l3).2.2
  have he5 := stack_transfer (ramTmp 0) (fun k => decide (k = ramReg dst)) l4
  have hf5 : transferStore (ramTmp 0) (fun k => decide (k = ramReg dst)) l4 =
      Function.update l (ramReg dst) (x.drop y.length).reverse := by
    funext k
    by_cases hd : k = ramReg dst
    · subst k; simp [transferStore, l4, l3, ramReg, ramTmp]
    by_cases h0 : k = ramTmp 0
    · subst k; simpa [transferStore, ramReg, ramTmp] using hr.2.2.2 0
    · simp [transferStore, l4, l3, hd, h0]
  rw [hf5] at he5
  have he := he1.seq (he2.seq (he3.seq (he4.seq he5)))
  refine ⟨_, _, ?_, he, ?_⟩
  · simp only [l4, l3, l2, l1, ramReg, ramTmp, Function.update_self,
      Function.update_of_ne (by simp : (Sum.inl (Sum.inr (0 : Fin 6)) : RAMWire V) ≠
        Sum.inl (Sum.inl dst)),
      Function.update_of_ne (by simp : (Sum.inl (Sum.inl dst) : RAMWire V) ≠
        Sum.inl (Sum.inr (0 : Fin 6))), List.length_drop]
    change 6 * x.length + 3 + 1 + (6 * y.length + 3 + 1 + (3 * y.length + 1 + 1 +
      (3 * (l (ramReg dst)).length + 1 + 1 + (3 * (x.length - y.length) + 1)))) ≤ _
    have hx := hr.1 i; have hy' := hr.1 j; have hd := hr.1 dst
    dsimp [x, y] at *; omega
  · simpa [x, y, hr.1 i, hr.1 j] using
      (ram_frames s l hr).1 dst (x.drop y.length).reverse

#print axioms solution
