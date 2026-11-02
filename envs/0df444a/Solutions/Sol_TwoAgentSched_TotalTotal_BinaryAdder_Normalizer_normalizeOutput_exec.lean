-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.BinaryAdder.Normalizer.normalizeOutput_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:43:55.659551+00:00
-- url     : https://prove2.me/submissions/3edf16fc-18d5-4e88-8ed3-80b682f0949c

import Theorems.Thm_CookPvsNP_stack_transfer
import Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdderNormalizer
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.BinaryAdder
open TwoAgentSched.TotalTotal.BinaryAdder.Normalizer

private theorem dropOutput_step (left right output carries : List BSym) :
    StackProg.applyAct dropOutputAct (store left right (.zero :: output) carries) =
      store left right output carries := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, dropOutputAct, store, StackAct.apply]

private theorem trimOutput_exec (left right output carries : List BSym) :
    trimOutput.Exec (store left right output carries)
      (store left right (output.dropWhile (fun x => x == BSym.zero)) carries)
      (3 * (output.takeWhile (fun x => x == BSym.zero)).length + 1) := by
  induction output with
  | nil =>
    apply StackProg.Exec.loopFalse
    rfl
  | cons x xs ih =>
    cases x with
    | zero =>
      have ht : zeroOnOutput (fun k => (store left right (.zero :: xs) carries k).head?) = true := by rfl
      have ha : (StackProg.act dropOutputAct).Exec (store left right (.zero :: xs) carries)
          (store left right xs carries) 1 := by
        rw [← dropOutput_step left right xs carries]
        exact StackProg.Exec.act _ _
      have hloop := StackProg.Exec.loopTrue ht ha ih
      simpa [trimOutput, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop
    | one =>
      apply StackProg.Exec.loopFalse
      rfl
    | minus =>
      apply StackProg.Exec.loopFalse
      rfl
    | sep =>
      apply StackProg.Exec.loopFalse
      rfl

theorem solution (output carries : List BSym) :
    normalizeOutput.Exec (store [] [] output carries)
      (store (output.dropWhile (fun x => x == BSym.zero)).reverse [] [] [.zero])
      (3 * (output.takeWhile (fun x => x == BSym.zero)).length +
       3 * (output.dropWhile (fun x => x == BSym.zero)).length + 3 * carries.length + 7) := by
  let zeroPrefix := output.takeWhile (fun x => x == BSym.zero)
  let rest := output.dropWhile (fun x => x == BSym.zero)
  have ht := trimOutput_exec [] [] output carries
  have hm := CookPvsNP.stack_transfer (2 : Fin 4) (fun k => decide (k = 0)) (store [] [] rest carries)
  have hmout : transferStore (2 : Fin 4) (fun k => decide (k = 0)) (store [] [] rest carries) =
      store rest.reverse [] [] carries := by
    funext k
    fin_cases k <;> simp [transferStore, store]
  rw [hmout] at hm
  have hc := CookPvsNP.stack_transfer (3 : Fin 4) (fun _ => false) (store rest.reverse [] [] carries)
  have hcout : transferStore (3 : Fin 4) (fun _ => false) (store rest.reverse [] [] carries) =
      store rest.reverse [] [] [] := by
    funext k
    fin_cases k <;> simp [transferStore, store]
  rw [hcout] at hc
  have hp : (pushProg (3 : Fin 4) BSym.zero).Exec (store rest.reverse [] [] [])
      (store rest.reverse [] [] [.zero]) 1 := by
    have he : StackProg.applyAct (fun _ k => if k = (3 : Fin 4) then .push BSym.zero else .keep)
        (store rest.reverse [] [] []) = store rest.reverse [] [] [.zero] := by
      funext k
      fin_cases k <;> simp [StackProg.applyAct, store, StackAct.apply]
    rw [← he]
    exact StackProg.Exec.act _ _
  have hseq := StackProg.Exec.seq ht (StackProg.Exec.seq hm (StackProg.Exec.seq hc hp))
  unfold normalizeOutput clearProg
  convert hseq using 1 <;> simp [zeroPrefix, rest, store] <;> omega
