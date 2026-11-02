-- Prove2me | solution 1 for TensorAdjacencyLookup8.lookupProg_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:29:47.983197+00:00
-- url     : https://prove2.me/submissions/f669d7c2-8e3e-4261-a70a-567b06c0b8d4

import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Definitions.Def_TensorAdjacencyLookup8
open CookPvsNP ProjSchedTW.Complexity TensorAdjacencyLookup8
set_option maxHeartbeats 1000000

private theorem upd (d dim row col out off tmp scratch x : List BSym) :
    Function.update (store d dim row col out off tmp scratch) 6 x = store d dim row col out off x scratch := by
  funext k; fin_cases k <;> rfl
private theorem upd5 (d dim row col out off tmp scratch x : List BSym) :
    Function.update (store d dim row col out off tmp scratch) 5 x = store d dim row col out x tmp scratch := by
  funext k; fin_cases k <;> rfl
private theorem flatrep (n m : ℕ) : (List.replicate n (List.replicate m BSym.one)).flatten = List.replicate (n*m) .one := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm, List.replicate_add]
private theorem skip_step (d dim row col out off tmp scratch : List BSym) (a b : BSym) :
    StackProg.applyAct skipAction (store d dim row col out (a::off) (b::tmp) scratch) = store d dim row col out off tmp scratch := by
  funext k; fin_cases k <;> rfl
private theorem skip_exec (d dim row col out scratch pre rest : List BSym) :
    StackProg.Exec (.loop hasOffsetAndData (.act skipAction))
      (store d dim row col out (List.replicate pre.length .one) (pre ++ rest) scratch)
      (store d dim row col out [] rest scratch) (3*pre.length+1) := by
  induction pre with
  | nil =>
    simpa using (StackProg.Exec.loopFalse (p := .act skipAction)
      (s := store d dim row col out [] rest scratch) (by rfl))
  | cons a pre ih =>
    have hguard : hasOffsetAndData
        (fun k => (store d dim row col out (.one :: List.replicate pre.length .one) (a :: (pre ++ rest)) scratch k).head?) = true := by rfl
    have hact : StackProg.Exec (.act skipAction)
        (store d dim row col out (.one :: List.replicate pre.length .one) (a :: (pre ++ rest)) scratch)
        (store d dim row col out (List.replicate pre.length .one) (pre ++ rest) scratch) 1 := by
      simpa only [skip_step] using (StackProg.Exec.act skipAction
        (store d dim row col out (.one :: List.replicate pre.length .one) (a :: (pre ++ rest)) scratch))
    simpa [List.replicate_succ, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (StackProg.Exec.loopTrue hguard hact ih)

theorem solution (v i j : ℕ) (data tail : List BSym)
    (hi : i < v) (hj : j < v) (hlen : data.length = v*v) :
    ∃ steps, steps ≤ 50*(v+1)^2 ∧
      lookupProg.Exec
        (store data (List.replicate v .one) (List.replicate i .one) (List.replicate j .one) tail [] [] [])
        (store data (List.replicate v .one) (List.replicate i .one) (List.replicate j .one)
          (data.getD (i*v+j) .zero :: tail) [] [] []) steps := by
  let dim := List.replicate v BSym.one
  let row := List.replicate i BSym.one
  let col := List.replicate j BSym.one
  let n := i*v+j
  have hn : n < data.length := by dsimp [n]; rw [hlen]; nlinarith
  have h1 : (copyProg (2 : Fin 8) 6 7).Exec (store data dim row col tail [] [] [])
      (store data dim row col tail [] row []) (6*i+3) := by
    simpa [store, row, upd] using (stack_copy (2 : Fin 8) 6 7 (by decide) (by decide) (by decide)
      (store data dim row col tail [] [] []) (by rfl))
  have h2 : (repeatCopyProg multiplyPorts).Exec (store data dim row col tail [] row [])
      (store data dim row col tail (List.replicate (i*v) .one) [] []) ((6*v+7)*i+1) := by
    have h := stack_repeat_copy multiplyPorts (store data dim row col tail [] row []) (by rfl)
    simpa [multiplyPorts, store, dim, row, flatrep, upd, upd5] using h
  have h3 : (copyProg (3 : Fin 8) 5 6).Exec
      (store data dim row col tail (List.replicate (i*v) .one) [] [])
      (store data dim row col tail (List.replicate n .one) [] []) (6*j+3) := by
    have h := stack_copy (3 : Fin 8) 5 6 (by decide) (by decide) (by decide)
      (store data dim row col tail (List.replicate (i*v) .one) [] []) (by rfl)
    rw [upd5] at h
    simpa [store, col, ← List.replicate_add, n, Nat.add_comm] using h
  have h4 : (copyProg (0 : Fin 8) 6 7).Exec
      (store data dim row col tail (List.replicate n .one) [] [])
      (store data dim row col tail (List.replicate n .one) data []) (6*(v*v)+3) := by
    have h := stack_copy (0 : Fin 8) 6 7 (by decide) (by decide) (by decide)
      (store data dim row col tail (List.replicate n .one) [] []) (by rfl)
    simpa [store, upd, hlen] using h
  have h5 : (StackProg.loop hasOffsetAndData (.act skipAction)).Exec
      (store data dim row col tail (List.replicate n .one) data [])
      (store data dim row col tail [] (data.drop n) []) (3*n+1) := by
    have h := skip_exec data dim row col tail [] (data.take n) (data.drop n)
    simpa [List.take_append_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] using h
  have hread : StackProg.applyAct readAction (store data dim row col tail [] (data.drop n) []) =
      store data dim row col (data.getD n .zero :: tail) [] (data.drop n) [] := by
    rw [List.drop_eq_getElem_cons hn, List.getD_eq_getElem data .zero hn]
    funext k; fin_cases k <;> rfl
  have h6 : (StackProg.act readAction).Exec (store data dim row col tail [] (data.drop n) [])
      (store data dim row col (data.getD n .zero :: tail) [] (data.drop n) []) 1 := by
    simpa only [hread] using StackProg.Exec.act readAction (store data dim row col tail [] (data.drop n) [])
  have h7 : (clearProg (6 : Fin 8)).Exec
      (store data dim row col (data.getD n .zero :: tail) [] (data.drop n) [])
      (store data dim row col (data.getD n .zero :: tail) [] [] []) (3*(data.drop n).length+1) := by
    simpa [store, upd] using (stack_basic_macros (6 : Fin 8)
      (store data dim row col (data.getD n .zero :: tail) [] (data.drop n) [])).2.2
  have hex := StackProg.Exec.seq h1 (StackProg.Exec.seq h2 (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 (StackProg.Exec.seq h5 (StackProg.Exec.seq h6 h7)))))
  refine ⟨(6*i+3) + ((6*v+7)*i+1) + (6*j+3) + (6*(v*v)+3) + (3*n+1) + 1 + (3*(data.drop n).length+1) + 6, ?_, ?_⟩
  · have hd : (data.drop n).length ≤ v*v := by simpa [hlen] using (List.length_drop_le n data)
    have hp := Nat.mul_le_mul_right v (Nat.le_of_lt hi)
    dsimp [n] at *
    nlinarith
  · convert hex using 1 <;> dsimp [lookupProg, dim, row, col, n] <;> omega
