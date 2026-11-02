-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.stack_tagged_gadget_exec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:15:10.188489+00:00
-- url     : https://prove2.me/submissions/e3a04337-e796-4971-9b2f-2b4e627b6de3

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_StackTaggedOutput
import Theorems.Thm_TwoAgentSched_TotalTotal_partition_tag_weight_encoding

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.StackTaggedOutput

private theorem push_step (a : BSym) (i d out : List BSym) :
    StackProg.applyAct (pushAct a) (store i d out) = store i d (a :: out) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, pushAct, store, StackAct.apply]

private theorem consume0_step (c : BSym) (i d out : List BSym) :
    StackProg.applyAct (consumeAct 0) (store (c :: i) d out) = store i d (.zero :: out) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, consumeAct, store, StackAct.apply]

private theorem consume1_step (c : BSym) (i d out : List BSym) :
    StackProg.applyAct (consumeAct 1) (store i (c :: d) out) = store i d (.zero :: out) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, consumeAct, store, StackAct.apply]

/-- The first counter emits a doubled zero run in linear time. -/
theorem doubleZero0_exec (i d out : List BSym) :
    (doubleZero 0).Exec (store i d out)
      (store [] d (List.replicate (2 * i.length) .zero ++ out)) (5 * i.length + 1) := by
  induction i generalizing out with
  | nil =>
    apply StackProg.Exec.loopFalse
    rfl
  | cons c i ih =>
    have ht : nonempty 0 (fun k => (store (c :: i) d out k).head?) = true := by rfl
    have ha : (StackProg.act (pushAct .zero)).Exec (store (c :: i) d out)
        (store (c :: i) d (.zero :: out)) 1 := by
      rw [← push_step]
      exact StackProg.Exec.act _ _
    have hb : (StackProg.act (consumeAct 0)).Exec (store (c :: i) d (.zero :: out))
        (store i d (.zero :: .zero :: out)) 1 := by
      rw [← consume0_step c i d (.zero :: out)]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue ht (StackProg.Exec.seq ha hb) (ih (.zero :: .zero :: out))
    have hrep (k : ℕ) (xs : List BSym) :
        List.replicate k BSym.zero ++ BSym.zero :: xs =
          BSym.zero :: (List.replicate k BSym.zero ++ xs) := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih]
    simp only [hrep] at hloop
    simpa [doubleZero, List.replicate_add, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- The second counter emits a doubled zero run in linear time. -/
theorem doubleZero1_exec (i d out : List BSym) :
    (doubleZero 1).Exec (store i d out)
      (store i [] (List.replicate (2 * d.length) .zero ++ out)) (5 * d.length + 1) := by
  induction d generalizing out with
  | nil =>
    apply StackProg.Exec.loopFalse
    rfl
  | cons c d ih =>
    have ht : nonempty 1 (fun k => (store i (c :: d) out k).head?) = true := by rfl
    have ha : (StackProg.act (pushAct .zero)).Exec (store i (c :: d) out)
        (store i (c :: d) (.zero :: out)) 1 := by
      rw [← push_step]
      exact StackProg.Exec.act _ _
    have hb : (StackProg.act (consumeAct 1)).Exec (store i (c :: d) (.zero :: out))
        (store i d (.zero :: .zero :: out)) 1 := by
      rw [← consume1_step c i d (.zero :: out)]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue ht (StackProg.Exec.seq ha hb) (ih (.zero :: .zero :: out))
    have hrep (k : ℕ) (xs : List BSym) :
        List.replicate k BSym.zero ++ BSym.zero :: xs =
          BSym.zero :: (List.replicate k BSym.zero ++ xs) := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih]
    simp only [hrep] at hloop
    simpa [doubleZero, List.replicate_add, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- The tagged-output program consumes both unary counters, emits the exact
    two zero runs and marker, and uses linear source-program time. -/
theorem taggedOutput_exec (i d out : List BSym) :
    taggedOutput.Exec (store i d out)
      (store [] [] (List.replicate (2 * i.length + 1) .zero ++ .one ::
        (List.replicate (2 * d.length + 1) .zero ++ out)))
      (5 * i.length + 5 * d.length + 9) := by
  let tail := List.replicate (2 * d.length) BSym.zero ++ out
  have hD : (doubleZero 1).Exec (store i d out) (store i [] tail)
      (5 * d.length + 1) := doubleZero1_exec i d out
  have hz : (StackProg.act (pushAct .zero)).Exec (store i [] tail)
      (store i [] (.zero :: tail)) 1 := by
    rw [← push_step .zero i [] tail]
    exact StackProg.Exec.act _ _
  have ho : (StackProg.act (pushAct .one)).Exec (store i [] (.zero :: tail))
      (store i [] (.one :: .zero :: tail)) 1 := by
    rw [← push_step .one i [] (.zero :: tail)]
    exact StackProg.Exec.act _ _
  have hI := doubleZero0_exec i [] (.one :: .zero :: tail)
  have hlast : (StackProg.act (pushAct .zero)).Exec
      (store [] [] (List.replicate (2 * i.length) .zero ++ .one :: .zero :: tail))
      (store [] [] (.zero :: (List.replicate (2 * i.length) .zero ++ .one :: .zero :: tail))) 1 := by
    rw [← push_step]
    exact StackProg.Exec.act _ _
  have hseq := StackProg.Exec.seq hD (StackProg.Exec.seq hz
    (StackProg.Exec.seq ho (StackProg.Exec.seq hI hlast)))
  convert hseq using 1 <;>
    simp [taggedOutput, tail, List.replicate_succ, List.append_assoc] <;> omega


end TwoAgentSched.TotalTotal.StackTaggedOutput

open TwoAgentSched.TotalTotal.StackTaggedOutput

/-- Execute the exact binary gadget code generator in linear stack-program time. -/
theorem solution (i d : List BSym) (m : ℕ) (hm : 0 < m) :
    taggedOutput.Exec (store i d (encNat m))
      (store [] [] (encNat (2 * (4 ^ (i.length + d.length + 1) * m + 4 ^ i.length))))
      (5 * i.length + 5 * d.length + 9) := by
  have h := taggedOutput_exec i d (encNat m)
  rw [← TwoAgentSched.TotalTotal.partition_tag_weight_encoding i.length d.length m hm] at h
  exact h
