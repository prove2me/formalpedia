-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.BinaryAdder.adderFullLoop_correct_and_cost
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:19:53.19942+00:00
-- url     : https://prove2.me/submissions/91ddeef5-2251-4641-9596-b6c19b979aba

import Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdder

open CookPvsNP ProjSchedTW.Complexity
namespace TwoAgentSched.TotalTotal.BinaryAdder

private theorem stepBoth (x y c : Bool) (left right output carries : List BSym) :
    adderStep.Exec (store (bitSym x :: left) (bitSym y :: right) output (bitSym c :: carries))
      (store left right (bitSym (sumBit x y c) :: output)
        (bitSym (carryBit x y c) :: bitSym c :: carries)) 1 := by
  have hstep : StackProg.applyAct addAct
      (store (bitSym x :: left) (bitSym y :: right) output (bitSym c :: carries)) =
      store left right (bitSym (sumBit x y c) :: output)
        (bitSym (carryBit x y c) :: bitSym c :: carries) := by
    funext k
    fin_cases k <;> cases x <;> cases y <;> cases c <;>
      simp [StackProg.applyAct, addAct, asBit, store, bitSym, sumBit, carryBit, StackAct.apply]
  rw [← hstep]
  exact StackProg.Exec.act _ _

private theorem stepLeft (x c : Bool) (left output carries : List BSym) :
    adderStep.Exec (store (bitSym x :: left) [] output (bitSym c :: carries))
      (store left [] (bitSym (sumBit x false c) :: output)
        (bitSym (carryBit x false c) :: bitSym c :: carries)) 1 := by
  have hstep : StackProg.applyAct addAct
      (store (bitSym x :: left) [] output (bitSym c :: carries)) =
      store left [] (bitSym (sumBit x false c) :: output)
        (bitSym (carryBit x false c) :: bitSym c :: carries) := by
    funext k
    fin_cases k <;> cases x <;> cases c <;>
      simp [StackProg.applyAct, addAct, asBit, store, bitSym, sumBit, carryBit, StackAct.apply]
  rw [← hstep]
  exact StackProg.Exec.act _ _

private theorem stepRight (y c : Bool) (right output carries : List BSym) :
    adderStep.Exec (store [] (bitSym y :: right) output (bitSym c :: carries))
      (store [] right (bitSym (sumBit false y c) :: output)
        (bitSym (carryBit false y c) :: bitSym c :: carries)) 1 := by
  have hstep : StackProg.applyAct addAct
      (store [] (bitSym y :: right) output (bitSym c :: carries)) =
      store [] right (bitSym (sumBit false y c) :: output)
        (bitSym (carryBit false y c) :: bitSym c :: carries) := by
    funext k
    fin_cases k <;> cases y <;> cases c <;>
      simp [StackProg.applyAct, addAct, asBit, store, bitSym, sumBit, carryBit, StackAct.apply]
  rw [← hstep]
  exact StackProg.Exec.act _ _

private theorem run : (left right : List Bool) → (c : Bool) → (output carries : List BSym) →
    ∃ finalCarryTail : List BSym,
      adderFullLoop.Exec
        (store (left.map bitSym) (right.map bitSym) output (bitSym c :: carries))
        (store [] [] (((addFullAux left right c).1.map bitSym).reverse ++ output)
          (bitSym (addFullAux left right c).2 :: finalCarryTail))
        (3 * max left.length right.length + 1)
  | [], [], c, output, carries => by
    refine ⟨carries, ?_⟩
    simpa [adderFullLoop, addFullAux] using
      (StackProg.Exec.loopFalse (p := adderStep) (s := store [] [] output (bitSym c :: carries))
        (test := eitherNonempty) (by rfl))
  | x :: xs, [], c, output, carries => by
    have ht : eitherNonempty (fun k =>
      (store (bitSym x :: xs.map bitSym) [] output (bitSym c :: carries) k).head?) = true := by rfl
    have ha := stepLeft x c (xs.map bitSym) output carries
    obtain ⟨rest, hrest⟩ := run xs [] (carryBit x false c) (bitSym (sumBit x false c) :: output) (bitSym c :: carries)
    have hloop := StackProg.Exec.loopTrue ht ha hrest
    refine ⟨rest, ?_⟩
    simpa [adderFullLoop, addFullAux, List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop
  | [], y :: ys, c, output, carries => by
    have ht : eitherNonempty (fun k =>
      (store [] (bitSym y :: ys.map bitSym) output (bitSym c :: carries) k).head?) = true := by rfl
    have ha := stepRight y c (ys.map bitSym) output carries
    obtain ⟨rest, hrest⟩ := run [] ys (carryBit false y c) (bitSym (sumBit false y c) :: output) (bitSym c :: carries)
    have hloop := StackProg.Exec.loopTrue ht ha hrest
    refine ⟨rest, ?_⟩
    simpa [adderFullLoop, addFullAux, List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop
  | x :: xs, y :: ys, c, output, carries => by
    have ht : eitherNonempty (fun k =>
      (store (bitSym x :: xs.map bitSym) (bitSym y :: ys.map bitSym) output (bitSym c :: carries) k).head?) = true := by rfl
    have ha := stepBoth x y c (xs.map bitSym) (ys.map bitSym) output carries
    obtain ⟨rest, hrest⟩ := run xs ys (carryBit x y c) (bitSym (sumBit x y c) :: output) (bitSym c :: carries)
    have hloop := StackProg.Exec.loopTrue ht ha hrest
    refine ⟨rest, ?_⟩
    simpa [adderFullLoop, addFullAux, List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop
termination_by left right _ _ _ => left.length + right.length

private theorem bwcons (x : Bool) (xs : List Bool) :
    bitWordValue (x :: xs) = bitValue x + 2 * bitWordValue xs := by
  simp [bitWordValue, Nat.ofDigits]

private theorem ident (x y c : Bool) :
    bitValue x + bitValue y + bitValue c = bitValue (sumBit x y c) + 2 * bitValue (carryBit x y c) := by
  cases x <;> cases y <;> cases c <;> decide

private theorem bwNil : bitWordValue [] = 0 := by simp [bitWordValue]
private theorem bvFalse : bitValue false = 0 := rfl

private theorem value : (left right : List Bool) → (c : Bool) →
    bitWordValue left + bitWordValue right + bitValue c =
      bitWordValue (addFullAux left right c).1 +
        2 ^ (max left.length right.length) * bitValue (addFullAux left right c).2
  | [], [], c => by simp [addFullAux, bitWordValue]
  | x :: xs, [], c => by
    have hh := value xs [] (carryBit x false c)
    have ha := ident x false c
    simp only [addFullAux, bwcons, bwNil, bvFalse, List.length_cons, List.length_nil, Nat.max_zero, Nat.zero_max, pow_succ] at *
    nlinarith
  | [], y :: ys, c => by
    have hh := value [] ys (carryBit false y c)
    have ha := ident false y c
    simp only [addFullAux, bwcons, bwNil, bvFalse, List.length_cons, List.length_nil, Nat.max_zero, Nat.zero_max, pow_succ] at *
    nlinarith
  | x :: xs, y :: ys, c => by
    have hh := value xs ys (carryBit x y c)
    have ha := ident x y c
    simp only [addFullAux, bwcons, List.length_cons, Nat.succ_max_succ, pow_succ] at *
    nlinarith
termination_by left right _ => left.length + right.length

end TwoAgentSched.TotalTotal.BinaryAdder
open TwoAgentSched.TotalTotal.BinaryAdder

theorem solution (left right : List Bool) (c : Bool) (output carries : List BSym) :
    ∃ finalCarryTail : List BSym,
      adderFullLoop.Exec
        (store (left.map bitSym) (right.map bitSym) output (bitSym c :: carries))
        (store [] [] (((addFullAux left right c).1.map bitSym).reverse ++ output)
          (bitSym (addFullAux left right c).2 :: finalCarryTail))
        (3 * max left.length right.length + 1) ∧
      bitWordValue left + bitWordValue right + bitValue c =
        bitWordValue (addFullAux left right c).1 +
          2 ^ (max left.length right.length) * bitValue (addFullAux left right c).2 := by
  obtain ⟨tail, h⟩ := run left right c output carries
  exact ⟨tail, h, value left right c⟩