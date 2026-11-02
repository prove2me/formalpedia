-- Prove2me | solution 1 for TensorCoordinateCountdown.countdownProg_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:01:40.69686+00:00
-- url     : https://prove2.me/submissions/1bca8d87-eccb-4103-ba39-57b1f4624bc0

import Theorems.Thm_CookPvsNP_stack_copy
import Definitions.Def_TensorCoordinateCountdown
open CookPvsNP ProjSchedTW.Complexity TensorCoordinateCountdown

theorem solution (maximum row column : ℕ)
    (hnonterminal : row > 0 ∨ column > 0) :
    countdownProg.Exec (store maximum row column)
      (store maximum (if column = 0 then row - 1 else row)
        (if column = 0 then maximum else column - 1))
      (if column = 0 then 6 * maximum + 6 else 2) := by
  cases column with
  | zero =>
    have hp : StackProg.applyAct (popAt 1) (store maximum row 0) = store maximum (row - 1) 0 := by
      funext k
      fin_cases k <;> cases row <;> simp [StackProg.applyAct, popAt, store, StackAct.apply, List.replicate]
    have hc := CookPvsNP.stack_copy (0 : Fin 4) 2 3 (by decide) (by decide) (by decide)
      (store maximum (row - 1) 0) (by simp [store])
    have hout : Function.update (store maximum (row - 1) 0) 2
        (store maximum (row - 1) 0 0 ++ store maximum (row - 1) 0 2) =
        store maximum (row - 1) maximum := by
      funext k
      fin_cases k <;> simp [store, Function.update]
    rw [hout] at hc
    have ha := StackProg.Exec.act (popAt 1) (store maximum row 0)
    rw [hp] at ha
    have hs := StackProg.Exec.seq ha hc
    have hb := StackProg.Exec.branchFalse (p := .act (popAt 2))
      (test := columnNonempty) (by simp [columnNonempty, store]) hs
    convert hb using 1 <;> simp [countdownProg, store] <;> omega
  | succ c =>
    have hp : StackProg.applyAct (popAt 2) (store maximum row (c+1)) = store maximum row c := by
      funext k
      fin_cases k <;> simp [StackProg.applyAct, popAt, store, StackAct.apply, List.replicate]
    have ha := StackProg.Exec.act (popAt 2) (store maximum row (c+1))
    rw [hp] at ha
    have hb := StackProg.Exec.branchTrue (q := .seq (.act (popAt 1)) (copyProg 0 2 3))
      (test := columnNonempty) (by simp [columnNonempty, store, List.replicate]) ha
    simpa [countdownProg] using hb
