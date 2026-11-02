-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.StackCompareDigits.correct_and_total
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:39:20.604186+00:00
-- url     : https://prove2.me/submissions/12ee98ac-0c0f-48a9-a578-ab5e4063eef2

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_StackCompareDigits

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity


set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.StackCompareDigits

/-- Comparison states accumulated while scanning two equally long strings
    from most significant to least significant bit. -/
def stateTrace : List Bool → List Bool → List BSym → List BSym
  | x :: xs, y :: ys, s :: states =>
      stateTrace xs ys (nextState s (digitSym x) (digitSym y) :: s :: states)
  | _, _, states => states

private theorem compareAct_step (x y : Bool) (xs ys : List BSym) (s : BSym) (ss : List BSym) :
    StackProg.applyAct compareAct (store (digitSym x :: xs) (digitSym y :: ys) (s :: ss)) =
      store xs ys (nextState s (digitSym x) (digitSym y) :: s :: ss) := by
  funext k
  fin_cases k <;> cases x <;> cases y <;>
    simp [StackProg.applyAct, compareAct, store, digitSym, StackAct.apply]

/-- Each compared digit pair costs three source-program steps plus one final
    guard; the complete state history is retained on the third stack. -/
theorem compareProg_exec (left right : List Bool) (hlen : left.length = right.length)
    (s : BSym) (ss : List BSym) :
    compareProg.Exec (store (left.map digitSym) (right.map digitSym) (s :: ss))
      (store [] [] (stateTrace left right (s :: ss))) (3 * left.length + 1) := by
  induction left generalizing right s ss with
  | nil =>
    have hr : right = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst right
    apply StackProg.Exec.loopFalse
    rfl
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      have ht : bothNonempty (fun k =>
          (store (digitSym x :: xs.map digitSym) (digitSym y :: ys.map digitSym) (s :: ss) k).head?) = true := by rfl
      have ha : (StackProg.act compareAct).Exec
          (store (digitSym x :: xs.map digitSym) (digitSym y :: ys.map digitSym) (s :: ss))
          (store (xs.map digitSym) (ys.map digitSym)
            (nextState s (digitSym x) (digitSym y) :: s :: ss)) 1 := by
        rw [← compareAct_step]
        exact StackProg.Exec.act _ _
      have hloop := StackProg.Exec.loopTrue ht ha
        (ih ys hlen' (nextState s (digitSym x) (digitSym y)) (s :: ss))
      simpa [compareProg, stateTrace, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop


/-- Comparison history for arbitrary stack symbols.  This total operation
    also describes malformed inputs and an initially empty state stack. -/
def stateTraceAny : List BSym → List BSym → List BSym → List BSym
  | x :: xs, y :: ys, states =>
      stateTraceAny xs ys (nextState (states.head?.getD .sep) x y :: states)
  | _, _, states => states

private theorem compareAct_step_any (x y : BSym) (xs ys states : List BSym) :
    StackProg.applyAct compareAct (store (x :: xs) (y :: ys) states) =
      store xs ys (nextState (states.head?.getD .sep) x y :: states) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, compareAct, store, StackAct.apply]

/-- The digit-pair loop terminates on every pair of symbol lists, including
    malformed words, after exactly three steps per consumed pair and a final
    guard. Unmatched suffixes are left on their respective stacks. -/
theorem compareProg_exec_any (left right states : List BSym) :
    compareProg.Exec (store left right states)
      (store (left.drop right.length) (right.drop left.length) (stateTraceAny left right states))
      (3 * min left.length right.length + 1) := by
  induction left generalizing right states with
  | nil =>
    simpa [compareProg, stateTraceAny] using
      (StackProg.Exec.loopFalse (test := bothNonempty) (p := .act compareAct)
        (s := store [] right states) (by rfl))
  | cons x xs ih =>
    cases right with
    | nil =>
      simpa [compareProg, stateTraceAny] using
        (StackProg.Exec.loopFalse (test := bothNonempty) (p := .act compareAct)
          (s := store (x :: xs) [] states) (by rfl))
    | cons y ys =>
      have ht : bothNonempty (fun k => (store (x :: xs) (y :: ys) states k).head?) = true := by rfl
      have ha : (StackProg.act compareAct).Exec (store (x :: xs) (y :: ys) states)
          (store xs ys (nextState (states.head?.getD .sep) x y :: states)) 1 := by
        rw [← compareAct_step_any]
        exact StackProg.Exec.act _ _
      have hloop := StackProg.Exec.loopTrue ht ha
        (ih ys (nextState (states.head?.getD .sep) x y :: states))
      simpa [compareProg, stateTraceAny, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hloop



def lengthResult (left right states : List BSym) : List BSym :=
  match left, right with
  | [], _ :: _ => .zero :: states
  | _ :: _, [] => .one :: states
  | _, _ => states

private theorem markAct_step (a : BSym) (left right states : List BSym) :
    StackProg.applyAct (markAct a) (store left right states) = store left right (a :: states) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markAct, store, StackAct.apply]

private theorem keepAct_step (left right states : List BSym) :
    StackProg.applyAct keepAct (store left right states) = store left right states := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, keepAct, store, StackAct.apply]

/-- The length finalizer terminates on arbitrary inputs in at most three steps. -/
theorem finishLength_exec (left right states : List BSym) :
    ∃ steps ≤ 3, finishLength.Exec (store left right states)
      (store left right (lengthResult left right states)) steps := by
  cases left with
  | nil =>
    cases right with
    | nil =>
      have hL : leftShort (fun k => (store [] [] states k).head?) = false := by rfl
      have hR : rightShort (fun k => (store [] [] states k).head?) = false := by rfl
      have hact : (StackProg.act keepAct).Exec (store [] [] states) (store [] [] states) 1 := by
        rw [← keepAct_step [] [] states]
        exact StackProg.Exec.act _ _
      have hin := StackProg.Exec.branchFalse (p := .act (markAct .one)) hR hact
      have hout := StackProg.Exec.branchFalse (p := .act (markAct .zero)) hL hin
      exact ⟨3, by omega, by simpa [finishLength, lengthResult] using hout⟩
    | cons y ys =>
      have hL : leftShort (fun k => (store [] (y :: ys) states k).head?) = true := by rfl
      have hact : (StackProg.act (markAct .zero)).Exec (store [] (y :: ys) states)
          (store [] (y :: ys) (.zero :: states)) 1 := by
        rw [← markAct_step .zero [] (y :: ys) states]
        exact StackProg.Exec.act _ _
      have hout := StackProg.Exec.branchTrue
        (q := .branch rightShort (.act (markAct .one)) (.act keepAct)) hL hact
      exact ⟨2, by omega, by simpa [finishLength, lengthResult] using hout⟩
  | cons x xs =>
    cases right with
    | nil =>
      have hL : leftShort (fun k => (store (x :: xs) [] states k).head?) = false := by rfl
      have hR : rightShort (fun k => (store (x :: xs) [] states k).head?) = true := by rfl
      have hact : (StackProg.act (markAct .one)).Exec (store (x :: xs) [] states)
          (store (x :: xs) [] (.one :: states)) 1 := by
        rw [← markAct_step .one (x :: xs) [] states]
        exact StackProg.Exec.act _ _
      have hin := StackProg.Exec.branchTrue (q := .act keepAct) hR hact
      have hout := StackProg.Exec.branchFalse (p := .act (markAct .zero)) hL hin
      exact ⟨3, by omega, by simpa [finishLength, lengthResult] using hout⟩
    | cons y ys =>
      have hL : leftShort (fun k => (store (x :: xs) (y :: ys) states k).head?) = false := by rfl
      have hR : rightShort (fun k => (store (x :: xs) (y :: ys) states k).head?) = false := by rfl
      have hact : (StackProg.act keepAct).Exec (store (x :: xs) (y :: ys) states)
          (store (x :: xs) (y :: ys) states) 1 := by
        rw [← keepAct_step (x :: xs) (y :: ys) states]
        exact StackProg.Exec.act _ _
      have hin := StackProg.Exec.branchFalse (p := .act (markAct .one)) hR hact
      have hout := StackProg.Exec.branchFalse (p := .act (markAct .zero)) hL hin
      exact ⟨3, by omega, by simpa [finishLength, lengthResult] using hout⟩

/-- The full comparator halts on every input, even when it is not a binary
    code, in at most three steps per paired symbol plus five fixed steps. -/
theorem compareFullProg_total (left right states : List BSym) :
    ∃ steps ≤ 3 * min left.length right.length + 5,
      compareFullProg.Exec (store left right states)
        (store (left.drop right.length) (right.drop left.length)
          (lengthResult (left.drop right.length) (right.drop left.length)
            (stateTraceAny left right states))) steps := by
  obtain ⟨k, hk, hfinish⟩ := finishLength_exec (left.drop right.length) (right.drop left.length)
    (stateTraceAny left right states)
  refine ⟨(3 * min left.length right.length + 1) + 1 + k, by omega, ?_⟩
  exact StackProg.Exec.seq (compareProg_exec_any left right states) hfinish


/-- The comparison state determined by the first unequal digit. -/
def lexState : List Bool → List Bool → BSym
  | false :: _, true :: _ => .zero
  | true :: _, false :: _ => .one
  | _ :: xs, _ :: ys => lexState xs ys
  | _, _ => .sep

private theorem stateTrace_locked (left right : List Bool) (s : BSym) (ss : List BSym)
    (hs : s ≠ .sep) : (stateTrace left right (s :: ss)).head? = some s := by
  induction left generalizing right ss with
  | nil => rfl
  | cons x xs ih =>
    cases right with
    | nil => rfl
    | cons y ys =>
      simpa [stateTrace, nextState, hs] using ih ys (s :: ss)

/-- The top state after comparison is exactly the first-difference
    lexicographic comparison of the two MSB-first bit lists. -/
theorem stateTrace_head (left right : List Bool) (ss : List BSym) :
    (stateTrace left right (.sep :: ss)).head? = some (lexState left right) := by
  induction left generalizing right ss with
  | nil => cases right <;> rfl
  | cons x xs ih =>
    cases right with
    | nil => cases x <;> rfl
    | cons y ys =>
      cases x <;> cases y
      · simpa [stateTrace, lexState, nextState, digitSym] using ih ys (.sep :: ss)
      · simpa [stateTrace, lexState, nextState, digitSym] using
          stateTrace_locked xs ys .zero (.sep :: ss) (by decide)
      · simpa [stateTrace, lexState, nextState, digitSym] using
          stateTrace_locked xs ys .one (.sep :: ss) (by decide)
      · simpa [stateTrace, lexState, nextState, digitSym] using ih ys (.sep :: ss)



/-- Interpret a most-significant-bit-first bit list as a natural number. -/
def msbValue (bits : List Bool) : ℕ :=
  Nat.ofDigits 2 (bits.reverse.map (fun b => if b then 1 else 0))

private theorem msbValue_cons (b : Bool) (bits : List Bool) :
    msbValue (b :: bits) = msbValue bits + 2 ^ bits.length * (if b then 1 else 0) := by
  simp [msbValue, List.reverse_cons, List.map_append, Nat.ofDigits_append]

private theorem msbValue_lt_pow (bits : List Bool) : msbValue bits < 2 ^ bits.length := by
  have hd : ∀ x ∈ bits.reverse.map (fun b => if b then 1 else 0), x < 2 := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> simp
  simpa [msbValue] using Nat.ofDigits_lt_base_pow_length (b := 2) (by decide) hd

/-- For equal-length MSB-first inputs, the comparator's less marker is exactly
    strict numerical order of the encoded bit strings. -/
theorem lexState_lt_iff (left right : List Bool) (hlen : left.length = right.length) :
    lexState left right = .zero ↔ msbValue left < msbValue right := by
  induction left generalizing right with
  | nil =>
    have hr : right = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst right
    simp [lexState, msbValue]
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      have hx := msbValue_lt_pow xs
      have hy := msbValue_lt_pow ys
      have hc := ih ys hl
      cases x <;> cases y <;>
        simp [lexState, msbValue_cons, hl] at * <;> omega



/-- Canonical codes with strictly fewer bits represent strictly smaller numbers. -/
theorem bits_length_lt_implies_lt (m n : ℕ) (h : m.bits.length < n.bits.length) : m < n := by
  by_contra hn
  have hs := Nat.size_le_size (Nat.le_of_not_gt hn)
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len] at hs
  omega

/-- Reading the reversed canonical binary digits recovers the encoded number. -/
theorem msbValue_bits_reverse (n : ℕ) : msbValue n.bits.reverse = n := by
  have hmap : n.bits.map (fun b => bif b then (1 : ℕ) else 0) =
      n.bits.map (fun b => if b then (1 : ℕ) else 0) := by
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  have h := Nat.ofDigits_digits 2 n
  rw [Nat.digits_two_eq_bits, hmap] at h
  simpa [msbValue] using h

/-- Equal-length canonical binary codes compare lexicographically in exactly
    the same order as the represented natural numbers. -/
theorem canonical_lex_lt_iff (m n : ℕ) (hlen : m.bits.length = n.bits.length) :
    lexState m.bits.reverse n.bits.reverse = .zero ↔ m < n := by
  have he : m.bits.reverse.length = n.bits.reverse.length := by simpa using hlen
  simpa [msbValue_bits_reverse] using lexState_lt_iff m.bits.reverse n.bits.reverse he



/-- The raw-symbol machine trace agrees with the Boolean trace on binary inputs. -/
theorem stateTraceAny_map (left right : List Bool) (s : BSym) (ss : List BSym) :
    stateTraceAny (left.map digitSym) (right.map digitSym) (s :: ss) =
      stateTrace left right (s :: ss) := by
  induction left generalizing right s ss with
  | nil => cases right <;> rfl
  | cons x xs ih =>
    cases right with
    | nil => rfl
    | cons y ys =>
      simp [stateTraceAny, stateTrace, ih]



/-- On canonical most-significant-first inputs, the finalized marker is less
    exactly when the represented first natural number is smaller. -/
theorem canonical_result_lt_iff (m n : ℕ) :
    let l := m.bits.reverse.map digitSym
    let r := n.bits.reverse.map digitSym
    (lengthResult (l.drop r.length) (r.drop l.length)
      (stateTraceAny l r [.sep])).head? = some .zero ↔ m < n := by
  let l := m.bits.reverse.map digitSym
  let r := n.bits.reverse.map digitSym
  change (lengthResult (l.drop r.length) (r.drop l.length)
    (stateTraceAny l r [.sep])).head? = some .zero ↔ m < n
  rcases lt_trichotomy m.bits.length n.bits.length with hl | he | hg
  · have hleft : l.drop r.length = [] := by
      apply List.drop_eq_nil_of_le
      simpa [l, r] using hl.le
    have hright : r.drop l.length ≠ [] := by
      intro hz
      have hlen := congrArg List.length hz
      simp [l, r] at hlen
      omega
    have hmn : m < n := bits_length_lt_implies_lt m n hl
    cases hR : r.drop l.length with
    | nil => exact (hright hR).elim
    | cons c cs => simp [hleft, hR, lengthResult, hmn]
  · have hleft : l.drop r.length = [] := by
      apply List.drop_eq_nil_of_le
      simpa [l, r] using he.le
    have hright : r.drop l.length = [] := by
      apply List.drop_eq_nil_of_le
      simpa [l, r] using he.symm.le
    rw [hleft, hright]
    change (stateTraceAny l r [.sep]).head? = some .zero ↔ m < n
    have htrace := stateTraceAny_map m.bits.reverse n.bits.reverse .sep []
    change stateTraceAny l r [.sep] = stateTrace m.bits.reverse n.bits.reverse [.sep] at htrace
    rw [htrace, stateTrace_head]
    simpa using canonical_lex_lt_iff m n he
  · have hright : r.drop l.length = [] := by
      apply List.drop_eq_nil_of_le
      simpa [l, r] using hg.le
    have hleft : l.drop r.length ≠ [] := by
      intro hz
      have hlen := congrArg List.length hz
      simp [l, r] at hlen
      omega
    have hnm : n < m := bits_length_lt_implies_lt n m hg
    have hnot : ¬ m < n := Nat.not_lt_of_ge (Nat.le_of_lt hnm)
    cases hL : l.drop r.length with
    | nil => exact (hleft hL).elim
    | cons c cs => simp [hL, hright, lengthResult, hnot]



/-- A concrete finite-stack execution compares any two canonical naturals:
    its final marker is less exactly when the first natural is smaller. -/
theorem compare_canonical_exec (m n : ℕ) :
    ∃ (steps : ℕ) (left right result : List BSym),
      steps ≤ 3 * min m.bits.length n.bits.length + 5 ∧
      compareFullProg.Exec
        (store (m.bits.reverse.map digitSym) (n.bits.reverse.map digitSym) [.sep])
        (store left right result) steps ∧
      (result.head? = some .zero ↔ m < n) := by
  obtain ⟨steps, hbound, hexec⟩ := compareFullProg_total
    (m.bits.reverse.map digitSym) (n.bits.reverse.map digitSym) [.sep]
  refine ⟨steps, _, _, _, ?_, hexec, ?_⟩
  · simpa using hbound
  · exact canonical_result_lt_iff m n


end TwoAgentSched.TotalTotal.StackCompareDigits

open TwoAgentSched.TotalTotal.StackCompareDigits

theorem solution :
    (∀ m n : ℕ, ∃ (steps : ℕ) (left right result : List BSym),
      steps ≤ 3 * min m.bits.length n.bits.length + 5 ∧
      compareFullProg.Exec
        (store (m.bits.reverse.map digitSym) (n.bits.reverse.map digitSym) [.sep])
        (store left right result) steps ∧
      (result.head? = some .zero ↔ m < n)) ∧
    (∀ left right states : List BSym, ∃ (out : Fin 3 → List BSym) (steps : ℕ),
      compareFullProg.Exec (store left right states) out steps ∧
        steps ≤ 3 * min left.length right.length + 5) := by
  constructor
  · exact compare_canonical_exec
  · intro left right states
    obtain ⟨steps, hbound, hexec⟩ := compareFullProg_total left right states
    exact ⟨_, steps, hexec, hbound⟩
