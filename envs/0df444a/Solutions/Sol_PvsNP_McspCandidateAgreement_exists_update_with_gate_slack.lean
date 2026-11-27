-- Prove2me | solution 1 for PvsNP.McspCandidateAgreement.exists_update_with_gate_slack
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T05:55:39.477876+00:00
-- url     : https://prove2.me/submissions/82b2179a-db55-4d74-9b1e-c8d265936d76

import Definitions.Def_NativeCircuitExtensionSemantics
set_option autoImplicit false
open PvsNP PvsNP.SuccinctCircuits PvsNP.McspCandidateAgreement

namespace PvsNP.SuccinctCircuits

theorem evalRegisters_append (g h : List Gate) (w : Str) :
    evalRegisters (g ++ h) w = evalRegisters h (evalRegisters g w) :=
  List.foldl_append

theorem evalRegisters_single (g : Gate) (w : Str) :
    evalRegisters [g] w = gateValue g w :: w := rfl

theorem evalRegisters_suffix (gs : List Gate) (w : Str) :
    ∃ fresh : Str, fresh.length = gs.length ∧ evalRegisters gs w = fresh ++ w := by
  induction gs generalizing w with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨fresh, hsize, hout⟩ := ih (gateValue g w :: w)
    refine ⟨fresh ++ [gateValue g w], by simp [hsize], ?_⟩
    change evalRegisters gs (gateValue g w :: w) = _
    rw [hout, List.append_assoc]
    rfl

def wireAt (w : Str) (i : ℕ) : Bool := w[i]?.getD false

theorem wireAt_shift (gs : List Gate) (w : Str) (i : ℕ) :
    wireAt (evalRegisters gs w) (gs.length + i) = wireAt w i := by
  obtain ⟨fresh, hsize, hout⟩ := evalRegisters_suffix gs w
  unfold wireAt
  rw [hout, List.getElem?_append_right (by omega)]
  congr 2
  omega

inductive AddGate | conjoin | disjoin

def AddGate.opcode : AddGate → ℕ
  | .conjoin => 3
  | .disjoin => 4

def AddGate.value : AddGate → Bool → Bool → Bool
  | .conjoin => (· && ·)
  | .disjoin => (· || ·)

inductive Formula
  | lit (b : Bool)
  | input (i : ℕ)
  | neg (f : Formula)
  | combine (op : AddGate) (f g : Formula)

def Formula.eval : Formula → Str → Bool
  | .lit b, _ => b
  | .input i, w => wireAt w i
  | .neg f, w => !(f.eval w)
  | .combine op f g, w => op.value (f.eval w) (g.eval w)

end PvsNP.SuccinctCircuits

namespace PvsNP.McspCandidateAgreement

open McspPadding SuccinctCircuits

private theorem zero_address_bit (n : ℕ) (i : Fin (2^(n+1))) :
    indexAssignment (n+1) i 0 = i.val.testBit n := by
  simp [indexAssignment]

/-- The native MCSP decoder puts exactly the selector-zero assignments before its midpoint. -/
theorem before_midpoint_iff (n : ℕ) (i : Fin (2^(n+1))) :
    i.val < 2^n ↔ indexAssignment (n+1) i 0 = false := by
  rw [zero_address_bit]
  constructor
  · exact Nat.testBit_lt_two_pow
  · intro h
    by_contra! h'
    have upper := i.isLt
    rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h' upper] at h
    contradiction

def lowIndex {n : ℕ} (i : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨i.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private theorem tail_bits {n : ℕ} (i : Fin (2^(n+1))) :
    (fun j : Fin n => indexAssignment (n+1) i j.succ) = indexAssignment n (lowIndex i) := by
  funext j
  change i.val.testBit (n+1-1-(j.val+1)) = (i.val % 2^n).testBit (n-1-j.val)
  rw [Nat.testBit_mod_two_pow, show n+1-1-(j.val+1) = n-1-j.val by omega]
  simp [show n-1-j.val < n by omega]

private theorem split_value {n : ℕ} (i : Fin (2^(n+1))) :
    i.val = (if indexAssignment (n+1) i 0 then 2^n else 0) + (lowIndex i).val := by
  have upper : i.val < 2^n * 2 := by simpa only [pow_succ] using i.isLt
  cases head : indexAssignment (n+1) i 0
  · change i.val = 0 + i.val % 2^n
    rw [Nat.zero_add,Nat.mod_eq_of_lt ((before_midpoint_iff _ _).mpr head)]
  · have large : 2^n ≤ i.val := by
      by_contra! small
      exact Bool.noConfusion (((before_midpoint_iff _ _).mp small).symm.trans head)
    have rest : i.val - 2^n < 2^n := by omega
    change i.val = 2^n + i.val % 2^n
    rw [Nat.mod_eq_sub_mod large,Nat.mod_eq_of_lt rest]
    omega

/-- An explicit circuit-formula comparison against the fixed binary cut.
The first bit of the assignment is the most significant one. -/
def atOrAfter : (n : ℕ) → Fin (2^n) → ℕ → Formula
  | 0, _, _ => .lit true
  | n+1, i, offset =>
    .combine (if indexAssignment (n+1) i 0 then .conjoin else .disjoin)
      (.input offset) (atOrAfter n (lowIndex i) (offset+1))

private theorem atOrAfter_correct (n : ℕ) (cut i : Fin (2^n)) (before : Str) :
    (atOrAfter n cut before.length).eval (before ++ List.ofFn (indexAssignment n i)) =
      decide (cut.val ≤ i.val) := by
  induction n generalizing before with
  | zero => simp [atOrAfter,Formula.eval]
  | succ n ih =>
    let lead := indexAssignment (n+1) i 0
    have w : List.ofFn (indexAssignment (n+1) i) =
        lead :: List.ofFn (indexAssignment n (lowIndex i)) := by
      rw [List.ofFn_succ,tail_bits]
    have next := ih (lowIndex cut) (lowIndex i) (before ++ [lead])
    have cutValue := split_value cut
    have addrValue := split_value i
    have wire : wireAt (before ++ lead :: List.ofFn (indexAssignment n (lowIndex i)))
        before.length = lead := by simp [wireAt]
    rw [w,atOrAfter,Formula.eval,Formula.eval,wire]
    rw [show before ++ lead :: List.ofFn (indexAssignment n (lowIndex i)) =
      (before ++ [lead]) ++ List.ofFn (indexAssignment n (lowIndex i)) by simp [List.append_assoc]]
    have offset : before.length+1 = (before ++ [lead]).length := by simp
    rw [offset,next]
    have csmall := (lowIndex cut).isLt
    have ismall := (lowIndex i).isLt
    dsimp [lead] at *
    cases x : indexAssignment (n+1) cut 0 <;> cases y : indexAssignment (n+1) i 0
      <;> simp [x,y,AddGate.value] at *
      <;> omega

private def thresholdGates : (n : ℕ) → Fin (2^n) → ℕ → ℕ → List Gate
  | 0, _, _, _ => [(1,0,0)]
  | n+1, cut, offset, before =>
    let tail := thresholdGates n (lowIndex cut) (offset+1) before
    let op := if indexAssignment (n+1) cut 0 then AddGate.conjoin else AddGate.disjoin
    tail ++ [(op.opcode, tail.length+(before+offset),0)]

private theorem thresholdGates_size (n : ℕ) (cut : Fin (2^n)) (offset before : ℕ) :
    (thresholdGates n cut offset before).length = n+1 := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    rw [thresholdGates,List.length_append,ih]
    rfl

private theorem direct_gate_value (op : AddGate) (w : Str) (j : ℕ) :
    gateValue (op.opcode,j,0) w = op.value (wireAt w j) (wireAt w 0) := by
  cases op <;> rfl

private theorem thresholdGates_correct (n : ℕ) (cut : Fin (2^n)) (offset : ℕ) (before w : Str) :
    wireAt (evalRegisters (thresholdGates n cut offset before.length) (before++w)) 0 =
      (atOrAfter n cut offset).eval w := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    let tail := thresholdGates n (lowIndex cut) (offset+1) before.length
    let op := if indexAssignment (n+1) cut 0 then AddGate.conjoin else AddGate.disjoin
    rw [thresholdGates,evalRegisters_append,evalRegisters_single]
    change gateValue (op.opcode,tail.length+(before.length+offset),0)
      (evalRegisters tail (before++w)) = _
    have input : wireAt (before++w) (before.length+offset) = wireAt w offset := by
      unfold wireAt
      rw [List.getElem?_append_right (by omega)]
      simp
    rw [direct_gate_value,wireAt_shift,input,ih]
    rfl

def forceFrom {n : ℕ} (old : List Gate) (cut : Fin (2^n)) (b : Bool) : List Gate :=
  let cmp := thresholdGates n cut 0 old.length
  old ++ cmp ++ if b then [(4,cmp.length,0)] else [(2,0,0),(3,cmp.length+1,0)]

private theorem atOrAfter_zero_correct (n : ℕ) (cut i : Fin (2^n)) :
    (atOrAfter n cut 0).eval (List.ofFn (indexAssignment n i)) = decide (cut.val ≤ i.val) :=
  atOrAfter_correct n cut i []

theorem forceFrom_size {n : ℕ} (old : List Gate) (cut : Fin (2^n)) (b : Bool) :
    (forceFrom old cut b).length = old.length+n+1+(if b then 1 else 2) := by
  have cmp := thresholdGates_size n cut 0 old.length
  cases b <;> simp [forceFrom,cmp] <;> omega

theorem forceFrom_value {n : ℕ} (old : List Gate) (cut i : Fin (2^n)) (b : Bool) :
    valueAt (forceFrom old cut b) i =
      if cut.val ≤ i.val then b else valueAt old i := by
  let w := List.ofFn (indexAssignment n i)
  let cmp := thresholdGates n cut 0 old.length
  let regs := evalRegisters cmp (evalRegisters old w)
  obtain ⟨built,bsize,hreg⟩ := evalRegisters_suffix old w
  have cmp_value : wireAt regs 0 = decide (cut.val ≤ i.val) := by
    change wireAt (evalRegisters cmp (evalRegisters old w)) 0 = _
    rw [hreg]
    have equal := thresholdGates_correct n cut 0 built w
    rw [bsize] at equal
    exact equal.trans (atOrAfter_zero_correct n cut i)
  have old_value : wireAt regs cmp.length = valueAt old i := by
    change wireAt (evalRegisters cmp (evalRegisters old w)) cmp.length = _
    rw [show cmp.length = cmp.length + 0 by omega,wireAt_shift]
    simp only [wireAt,valueAt,w,eval,List.head?_eq_getElem?]
  unfold valueAt
  change eval (old ++ cmp ++ if b then [(4,cmp.length,0)] else [(2,0,0),(3,cmp.length+1,0)]) w = _
  cases b
  · unfold eval
    rw [evalRegisters_append,evalRegisters_append]
    change (wireAt regs cmp.length && !wireAt regs 0) = _
    rw [cmp_value,old_value]
    unfold valueAt
    by_cases h : cut.val ≤ i.val <;> simp [h,eval]
  · unfold eval
    rw [evalRegisters_append,evalRegisters_append]
    change (wireAt regs cmp.length || wireAt regs 0) = _
    rw [cmp_value,old_value]
    unfold valueAt
    by_cases h : cut.val ≤ i.val <;> simp [h,eval]

/-- At every cut, a linear additive gate budget permits a compatible repair. -/
theorem extension_with_slack {n : ℕ} (old : List Gate) (cut : Fin (2^n)) (b : Bool) (s : ℕ)
    (slack : old.length+(n+1)+(if b then 1 else 2) ≤ s) :
    ∃ candidate, candidate.length ≤ s ∧ validUpdate old candidate cut b := by
  refine ⟨forceFrom old cut b,?_,?_⟩
  · rw [forceFrom_size]
    omega
  · constructor
    · intro i below
      rw [forceFrom_value,if_neg (by omega)]
    · rw [forceFrom_value,if_pos (Nat.le_refl _)]

end PvsNP.McspCandidateAgreement

theorem solution {n : ℕ} (old : List Gate) (cut : Fin (2^n)) (b : Bool) (s : ℕ)
    (slack : old.length+(n+1)+(if b then 1 else 2) ≤ s) :
    ∃ candidate, candidate.length ≤ s ∧ validUpdate old candidate cut b := by
  exact extension_with_slack old cut b s slack

#print axioms solution
