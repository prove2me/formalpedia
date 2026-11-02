-- Prove2me | solution 1 for TensorUnaryHalf.halfProg_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:42:59.054058+00:00
-- url     : https://prove2.me/submissions/98937cff-7d00-45ac-b9e8-a09867fba29c

import Definitions.Def_TensorUnaryHalf
import Mathlib.Tactic
open CookPvsNP ProjSchedTW.Complexity
namespace TensorUnaryHalf
lemma apply_first (xs q r : List BSym) :
    StackProg.applyAct takeFirst (store (.one :: xs) q r) = store xs q r := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, takeFirst, store, StackAct.apply]
lemma apply_pair (xs q r : List BSym) :
    StackProg.applyAct takePair (store (.one :: xs) q r) = store xs (.one :: q) r := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, takePair, store, StackAct.apply]
lemma apply_odd (q r : List BSym) :
    StackProg.applyAct markOdd (store [] q r) = store [] q (.one :: r) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markOdd, store, StackAct.apply]
lemma body_pair (xs q r : List BSym) :
    StackProg.Exec (.seq (.act takeFirst) (.branch nonempty (.act takePair) (.act markOdd)))
      (store (.one :: .one :: xs) q r) (store xs (.one :: q) r) 4 := by
  have h1 : StackProg.Exec (.act takeFirst) (store (.one :: .one :: xs) q r) (store (.one :: xs) q r) 1 := by
    simpa [apply_first] using StackProg.Exec.act takeFirst (store (.one :: .one :: xs) q r)
  have h2 : StackProg.Exec (.branch nonempty (.act takePair) (.act markOdd)) (store (.one :: xs) q r) (store xs (.one :: q) r) 2 := by
    have ha : StackProg.Exec (.act takePair) (store (.one :: xs) q r) (store xs (.one :: q) r) 1 := by
      simpa [apply_pair] using StackProg.Exec.act takePair (store (.one :: xs) q r)
    exact StackProg.Exec.branchTrue (by simp [nonempty, store]) ha
  exact StackProg.Exec.seq h1 h2
lemma body_odd (q r : List BSym) :
    StackProg.Exec (.seq (.act takeFirst) (.branch nonempty (.act takePair) (.act markOdd)))
      (store [.one] q r) (store [] q (.one :: r)) 4 := by
  have h1 : StackProg.Exec (.act takeFirst) (store [.one] q r) (store [] q r) 1 := by
    simpa [apply_first] using StackProg.Exec.act takeFirst (store [.one] q r)
  have h2 : StackProg.Exec (.branch nonempty (.act takePair) (.act markOdd)) (store [] q r) (store [] q (.one :: r)) 2 := by
    have ha : StackProg.Exec (.act markOdd) (store [] q r) (store [] q (.one :: r)) 1 := by
      simpa [apply_odd] using StackProg.Exec.act markOdd (store [] q r)
    exact StackProg.Exec.branchFalse (by simp [nonempty, store]) ha
  exact StackProg.Exec.seq h1 h2
end TensorUnaryHalf

theorem solution (n : ℕ) (quotientTail parityTail : List BSym) :
    TensorUnaryHalf.halfProg.Exec
      (TensorUnaryHalf.store (List.replicate n .one) quotientTail parityTail)
      (TensorUnaryHalf.store [] (List.replicate (n/2) .one ++ quotientTail)
        ((if n % 2 = 0 then [] else [.one]) ++ parityTail))
      (6*((n+1)/2)+1) := by
  induction n using Nat.twoStepInduction generalizing quotientTail parityTail with
  | zero =>
    simpa [TensorUnaryHalf.halfProg, TensorUnaryHalf.nonempty, TensorUnaryHalf.store] using
      (StackProg.Exec.loopFalse (p := .seq (.act TensorUnaryHalf.takeFirst) (.branch TensorUnaryHalf.nonempty (.act TensorUnaryHalf.takePair) (.act TensorUnaryHalf.markOdd))) (s := TensorUnaryHalf.store [] quotientTail parityTail) (by simp [TensorUnaryHalf.nonempty, TensorUnaryHalf.store]))
  | one =>
    have ht : TensorUnaryHalf.nonempty (fun k => (TensorUnaryHalf.store [.one] quotientTail parityTail k).head?) = true := by simp [TensorUnaryHalf.nonempty, TensorUnaryHalf.store]
    have hf := StackProg.Exec.loopFalse (test := TensorUnaryHalf.nonempty) (p := .seq (.act TensorUnaryHalf.takeFirst) (.branch TensorUnaryHalf.nonempty (.act TensorUnaryHalf.takePair) (.act TensorUnaryHalf.markOdd))) (s := TensorUnaryHalf.store [] quotientTail (.one :: parityTail)) (by simp [TensorUnaryHalf.nonempty, TensorUnaryHalf.store])
    have h := StackProg.Exec.loopTrue ht (TensorUnaryHalf.body_odd quotientTail parityTail) hf
    simpa [TensorUnaryHalf.halfProg] using h
  | more n ih₀ ih₁ =>
    have h := ih₀ (.one :: quotientTail) parityTail
    have ht : TensorUnaryHalf.nonempty (fun k => (TensorUnaryHalf.store (.one :: .one :: List.replicate n .one) quotientTail parityTail k).head?) = true := by simp [TensorUnaryHalf.nonempty, TensorUnaryHalf.store]
    have he := StackProg.Exec.loopTrue ht (TensorUnaryHalf.body_pair (List.replicate n .one) quotientTail parityTail) h
    have hd : (n+2)/2 = n/2+1 := by omega
    have hm : (n+2)%2 = n%2 := by omega
    have hc : 1+4+1+(6*((n+1)/2)+1) = 6*((n+2+1)/2)+1 := by omega
    have hq : List.replicate (n / 2 + 1) BSym.one ++ quotientTail = List.replicate (n/2) BSym.one ++ .one :: quotientTail := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    rw [hd, hm, hq, ← hc]
    simpa only [TensorUnaryHalf.halfProg, List.replicate_succ] using he
