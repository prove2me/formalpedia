-- Prove2me | solution 1 for Turing.MultiTapeTM.computableInPolyTime_to_tm2
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T06:43:20.774081+00:00
-- url     : https://prove2.me/submissions/1f33be4a-2ff1-4545-9347-4af90f0a8f94

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option linter.all false
set_option maxHeartbeats 4000000

/-!
Time-only adaptation of the Apache-2.0 Complexitylib reverse TM2 compiler by Erik Demaine.
Source: https://github.com/cslib-community/cslib-frontier/tree/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/TM2/Reverse
This file uses the archived Prove2Me native model and packaging lemmas. It drops the space
transfer, proves the needed auxiliary storage bound directly from the zipper steps, and
uses a Mathlib natural-coefficient polynomial for the final clock.
License: https://www.apache.org/licenses/LICENSE-2.0
-/


namespace Turing.TM2

/-- Execute one source step, keeping the last configuration after halting. -/
def stepTotal {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) (cfg : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  cfg.l.elim cfg (fun l => stepAux (M l) cfg.var cfg.stk)

end Turing.TM2
/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A bounded input zipper for the TM2 compiler

The left stack is reversed and the right stack includes the symbol under the head. A separate
flag distinguishes the left boundary from the first input symbol. An empty right stack with
the flag unset represents the right boundary, including the initial position on empty input.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Input`: the two stacks and the left-boundary flag.
* `Turing.MultiTapeTM.ToTM2.Input.Represents`: agreement with a native input and head position.

## Main results

* `Turing.MultiTapeTM.ToTM2.Input.represents_init`: initialization represents native position one.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.read_eq_inputSymbol`: reads agree with native reads.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.move`: moves agree, including boundary clamping.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A read-only input tape represented by two stacks and a left-boundary flag. -/
@[ext]
structure Input (Symbol : Type) where
  /-- Input symbols strictly to the left of the head, in reverse order. -/
  left : List Symbol
  /-- Input symbols from the head onward, in input order. -/
  right : List Symbol
  /-- Whether the head is at the blank before the input. -/
  atLeft : Bool
deriving Inhabited

namespace Input

variable {Symbol : Type}

/-- Start at native position one, also when the input is empty. -/
def init (input : List Symbol) : Input Symbol := ⟨[], input, false⟩

/-- Read the current input symbol, or a blank at either boundary. -/
def read (z : Input Symbol) : Option Symbol :=
  if z.atLeft then none else z.right.head?

/-- Move left, stopping at the blank before the input. -/
def moveLeft (z : Input Symbol) : Input Symbol :=
  if z.atLeft then z else
    match z.left with
    | [] => { z with atLeft := true }
    | a :: l => ⟨l, a :: z.right, false⟩

/-- Move right, stopping at the blank after the input. -/
def moveRight (z : Input Symbol) : Input Symbol :=
  if z.atLeft then { z with atLeft := false } else
    match z.right with
    | [] => z
    | a :: r => ⟨a :: z.left, r, false⟩

/-- Move the input head in the indicated direction. -/
def move (z : Input Symbol) : SignType → Input Symbol
  | .neg => z.moveLeft
  | .zero => z
  | .pos => z.moveRight

/-- The stacks reconstruct the input and locate the head at the native bounded position. -/
structure Represents (z : Input Symbol) (input : List Symbol)
    (pos : Fin (input.length + 2)) : Prop where
  /-- The two stacks hold exactly the original input. -/
  contents : z.left.reverse ++ z.right = input
  /-- No symbols precede the left boundary. -/
  left_nil : z.atLeft = true → z.left = []
  /-- Native positions count the left boundary as zero. -/
  pos_eq : pos.val = if z.atLeft then 0 else z.left.length + 1

/-- Initialization agrees with the native initial head position, including on empty input. -/
theorem represents_init (input : List Symbol) :
    (init input).Represents input ⟨1, by omega⟩ := by
  constructor <;> simp [init]

namespace Represents

variable {z : Input Symbol} {input : List Symbol} {pos : Fin (input.length + 2)}

/-- The stacks retain exactly the number of input symbols. -/
theorem length_eq (h : z.Represents input pos) :
    z.left.length + z.right.length = input.length := by
  simpa only [List.length_append, List.length_reverse] using congrArg List.length h.contents

/-- A zipper read agrees with indexing the original input at the native head position. -/
theorem read_eq_getElem? (h : z.Represents input pos) :
    z.read = if pos.val = 0 then none else input[pos.val - 1]? := by
  rcases z with ⟨l, r, b⟩
  cases b with
  | false =>
    have hp : pos.val = l.length + 1 := h.pos_eq
    have hi : input = l.reverse ++ r := h.contents.symm
    simp [read, hp, hi, List.getElem?_append_right, List.head?_eq_getElem?]
  | true => simp [read, h.pos_eq]

/-- A zipper read agrees with the input symbol of any represented native configuration. -/
theorem read_eq_inputSymbol {k : ℕ} {State : Type*} {cfg : Cfg k Symbol State input}
    (h : z.Represents input cfg.inputPos) : z.read = cfg.inputSymbol := by
  rw [h.read_eq_getElem?]
  unfold Cfg.inputSymbol
  have := cfg.inputPos.isLt
  split_ifs <;> grind

/-- Moving left preserves the representation, with clamping at the left boundary. -/
theorem moveLeft (h : z.Represents input pos) :
    z.moveLeft.Represents input (moveInputPos pos .neg) := by
  have hm := val_moveInputPos_eq pos .neg
  simp only [SignType.cast] at hm
  rcases z with ⟨l, r, b⟩
  cases b with
  | true =>
    refine ⟨h.contents, h.left_nil, ?_⟩
    have hp : pos.val = 0 := h.pos_eq
    change (moveInputPos pos .neg).val = 0
    omega
  | false =>
    cases l with
    | nil =>
      refine ⟨h.contents, ?_, ?_⟩
      · simp [Input.moveLeft]
      · have hp : pos.val = 1 := h.pos_eq
        change (moveInputPos pos .neg).val = 0
        omega
    | cons a l =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveLeft, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveLeft]
      · have hp : pos.val = (a :: l).length + 1 := h.pos_eq
        simp only [List.length_cons] at hp
        change (moveInputPos pos .neg).val = l.length + 1
        omega

/-- Moving right preserves the representation, with clamping at the right boundary. -/
theorem moveRight (h : z.Represents input pos) :
    z.moveRight.Represents input (moveInputPos pos .pos) := by
  have hm := val_moveInputPos_eq pos .pos
  simp only [SignType.cast] at hm
  have hlen := h.length_eq
  rcases z with ⟨l, r, b⟩
  change l.length + r.length = input.length at hlen
  cases b with
  | true =>
    have hl : l = [] := h.left_nil rfl
    subst l
    refine ⟨h.contents, ?_, ?_⟩
    · simp [Input.moveRight]
    · have hp : pos.val = 0 := h.pos_eq
      change (moveInputPos pos .pos).val = 1
      omega
  | false =>
    cases r with
    | nil =>
      refine ⟨h.contents, h.left_nil, ?_⟩
      have hp : pos.val = l.length + 1 := h.pos_eq
      simp only [List.length_nil, Nat.add_zero] at hlen
      change (moveInputPos pos .pos).val = l.length + 1
      omega
    | cons a r =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveRight, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveRight]
      · have hp : pos.val = l.length + 1 := h.pos_eq
        simp only [List.length_cons] at hlen
        change (moveInputPos pos .pos).val = l.length + 1 + 1
        omega

/-- Each zipper move simulates the corresponding native bounded head move. -/
theorem move (h : z.Represents input pos) (d : SignType) :
    (z.move d).Represents input (moveInputPos pos d) := by
  cases d with
  | neg => exact h.moveLeft
  | zero =>
    change z.Represents input (moveInputPos pos 0)
    rwa [moveInputPos_zero]
  | pos => exact h.moveRight

end Represents
end Input
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine, Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Bolton Bailey, Samuel Schlesinger
-/



/-!
# Raw two-stack work tapes

A work tape is stored as its current cell and two lists, nearest cell first. Blanks are retained:
moving beyond the stored interval extends it by one blank cell. Thus storage records the interval
visited by the head, independently of the number of times the machine revisits cells.
The relative read and representation proofs adapt the `BiTape` API of Bolton Bailey and
Samuel Schlesinger to raw lists.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.RawTape`: the current cell and the raw left and right stacks.
* `Turing.MultiTapeTM.ToTM2.RawTape.step`: native optional writing followed by head movement.
* `Turing.MultiTapeTM.ToTM2.RawTape.Represents`: correspondence with an integer-indexed native tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.RawTape.Represents.step`: preservation of native tape semantics.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A work tape with raw stacks, ordered from the head outwards. Trailing blanks are retained. -/
@[ext] structure RawTape (Symbol : Type*) where
  /-- The cell under the head. -/
  head : Option Symbol
  /-- Cells strictly to the left, nearest first. -/
  left : List (Option Symbol)
  /-- Cells strictly to the right, nearest first. -/
  right : List (Option Symbol)
  deriving DecidableEq

namespace RawTape

variable {Symbol : Type*}

/-- A blank tape, initially storing just the cell at its head. -/
def init : RawTape Symbol := ⟨none, [], []⟩

instance : Inhabited (RawTape Symbol) := ⟨init⟩

/-- Perform an optional native write: `none` preserves the cell and `some none` erases it. -/
def write (t : RawTape Symbol) (w : Option (Option Symbol)) : RawTape Symbol :=
  { t with head := w.getD t.head }

@[simp] theorem write_none (t : RawTape Symbol) : t.write none = t := rfl

@[simp] theorem head_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).head = w.getD t.head := rfl

/-- Move left, extending the stored interval by a blank when the left stack is empty. -/
def moveLeft (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.left.headD none, t.left.tail, t.head :: t.right⟩

/-- Move right, extending the stored interval by a blank when the right stack is empty. -/
def moveRight (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.right.headD none, t.head :: t.left, t.right.tail⟩

/-- Apply a native work-tape action, writing before moving. -/
def step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) : RawTape Symbol :=
  match a.2 with
  | .neg => (t.write a.1).moveLeft
  | .zero => t.write a.1
  | .pos => (t.write a.1).moveRight

/-- Read at an integer offset relative to the head; unstored cells are blank. -/
def read (t : RawTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => t.head
  | .ofNat (n + 1) => t.right.getD n none
  | .negSucc n => t.left.getD n none

/-- The raw tape agrees with a native tape whose head is at `pos`. -/
def Represents (t : RawTape Symbol) (native : ℤ → Option Symbol) (pos : ℤ) : Prop :=
  ∀ z, t.read z = native (pos + z)

@[simp] theorem read_zero (t : RawTape Symbol) : t.read 0 = t.head := by simp [read]

@[simp] theorem read_init (z : ℤ) : (init : RawTape Symbol).read z = none := by
  cases z with
  | ofNat n => cases n <;> simp [read, init]
  | negSucc n => simp [read, init]

theorem read_write (t : RawTape Symbol) (w : Option (Option Symbol)) (z : ℤ) :
    (t.write w).read z = if z = 0 then w.getD t.head else t.read z := by
  cases z with
  | ofNat n => cases n <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc n => simp [read, write]

theorem read_moveLeft (t : RawTape Symbol) (z : ℤ) :
    t.moveLeft.read z = t.read (z - 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n =>
      have he : (Int.ofNat (n + 1) : ℤ) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [he]
      cases n <;> rfl
  | negSucc n =>
    have he : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [he]
    cases l <;> rfl

theorem read_moveRight (t : RawTape Symbol) (z : ℤ) :
    t.moveRight.read z = t.read (z + 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    have he : (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [he]
    cases n <;> cases r <;> rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he]
      rfl

theorem Represents.head {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.head = native pos := by
  simpa using h 0

theorem Represents.init : (init : RawTape Symbol).Represents (fun _ => none) 0 := by
  intro z
  exact read_init z

theorem Represents.write {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (w : Option (Option Symbol)) :
    (t.write w).Represents (match w with
      | none => native
      | some s => Function.update native pos s) pos := by
  intro z
  rw [read_write]
  cases w with
  | none =>
    by_cases hz : z = 0
    · subst z; simpa using h 0
    · simpa [hz] using h z
  | some s =>
    by_cases hz : z = 0
    · subst z; simp
    · simpa [hz, show pos + z ≠ pos by omega] using h z

theorem Represents.moveLeft {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveLeft.Represents native (pos - 1) := by
  intro z
  rw [read_moveLeft, h]
  congr 1
  omega

theorem Represents.moveRight {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveRight.Represents native (pos + 1) := by
  intro z
  rw [read_moveRight, h]
  congr 1
  omega

/-- Raw execution preserves a native optional-write-and-move action, including erasing cells. -/
theorem Represents.step {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (a : Option (Option Symbol) × SignType) :
    (t.step a).Represents (match a.1 with
      | none => native
      | some s => Function.update native pos s) (pos + a.2) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write none
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write none).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write none).moveRight
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write (some _)
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write (some _)).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write (some _)).moveRight

@[simp] theorem left_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).left = t.left := rfl

@[simp] theorem right_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).right = t.right := rfl

@[simp] theorem length_left_moveLeft (t : RawTape Symbol) :
    t.moveLeft.left.length = t.left.length - 1 := by simp [moveLeft]

@[simp] theorem length_right_moveLeft (t : RawTape Symbol) :
    t.moveLeft.right.length = t.right.length + 1 := rfl

@[simp] theorem length_left_moveRight (t : RawTape Symbol) :
    t.moveRight.left.length = t.left.length + 1 := rfl

@[simp] theorem length_right_moveRight (t : RawTape Symbol) :
    t.moveRight.right.length = t.right.length - 1 := by simp [moveRight]

/-- The exact left-stack length after an action. -/
theorem length_left_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).left.length = match a.2 with
      | .neg => t.left.length - 1
      | .zero => t.left.length
      | .pos => t.left.length + 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_left_moveLeft, length_left_moveRight, left_write]

/-- The exact right-stack length after an action. -/
theorem length_right_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).right.length = match a.2 with
      | .neg => t.right.length + 1
      | .zero => t.right.length
      | .pos => t.right.length - 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_right_moveLeft, length_right_moveRight, right_write]

/-- The number of stored cells, including the current cell and stored blanks. -/
def span (t : RawTape Symbol) : ℕ := t.left.length + t.right.length + 1

@[simp] theorem span_init : (init : RawTape Symbol).span = 1 := rfl

@[simp] theorem span_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).span = t.span := rfl

/-- Storage grows only when the head moves beyond the previously stored interval. -/
theorem span_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span = t.span +
      if (a.2 = .neg ∧ t.left = []) ∨ (a.2 = .pos ∧ t.right = []) then 1 else 0 := by
  rcases a with ⟨w, d⟩
  cases d <;> cases hl : t.left <;> cases hr : t.right <;>
    simp [span, length_left_step, length_right_step, hl, hr,
      Nat.add_comm, Nat.add_left_comm]

theorem span_step_le (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span ≤ t.span + 1 := by
  rw [span_step]
  split_ifs <;> omega

end RawTape

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A finite stack program for deterministic multi-tape machines

The input uses a pair of binary stacks and a flag for the left boundary. Each two-sided work
tape uses two stacks over `Option Bool`, with its current cell in finite control. Output is
accumulated in reverse order. A separate cleanup phase empties all auxiliary stacks before
reversing the output and resetting the control to Mathlib's canonical `haltList` convention.

## Main definitions

* `Turing.TM2.selectList`, `Turing.TM2.select`: finite case analysis in a TM2 statement.
* `Turing.MultiTapeTM.ToTM2.machine`: the finite-alphabet stack machine.
* `Turing.MultiTapeTM.ToTM2.program`: its running, cleanup and output-reversal phases.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace Turing.TM2

open Stmt

variable {K : Type} {Γ : K → Type} {Λ State : Type}

/-- Finite case analysis compiles an arbitrary table on finite control to a fixed statement. -/
def selectList [DecidableEq State] (values : List State)
    (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  values.foldr (fun value rest => TM2.Stmt.branch (fun state => decide (state = value)) (table value) rest)
    halt

theorem stepAux_selectList [DecidableEq State] [DecidableEq K]
    (values : List State) (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) (h : state ∈ values) :
    stepAux (selectList values table) state store = stepAux (table state) state store := by
  induction values with
  | nil => simp at h
  | cons value values ih =>
    simp only [selectList, List.foldr_cons, stepAux]
    by_cases heq : state = value
    · subst value
      simp
    · simp only [heq, decide_false, Bool.cond_false]
      exact ih (List.mem_of_ne_of_mem heq h)

open scoped Classical in
/-- A table on a finite type uses only finitely many branches. -/
noncomputable def select [Fintype State] (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  selectList (Finset.univ.toList) table

theorem stepAux_select [Fintype State] [DecidableEq K]
    (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) :
    stepAux (select table) state store = stepAux (table state) state store := by
  classical
  exact stepAux_selectList _ _ _ _ (by simp)

end Turing.TM2

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- The four binary stacks and the two stacks for every work tape. -/
inductive Stack (k : ℕ) where
  | input | before | output | reversed
  | work (tape : Fin k) (right : Bool)
  deriving DecidableEq, Fintype

/-- Work stacks store blank cells explicitly; the input and output alphabets are binary. -/
abbrev Alphabet : Stack k → Type
  | .work _ _ => Option Bool
  | _ => Bool

instance (s : Stack k) : Fintype (Alphabet s) := by
  cases s <;> unfold Alphabet <;> infer_instance

/-- The three phases have no unbounded counters in their control. -/
inductive Label where
  | run | clean | reverse
  deriving DecidableEq

instance : Fintype Label := ⟨{.run, .clean, .reverse}, by intro l; cases l <;> simp⟩

/-- All unbounded data live on stacks. `symbol` and `busy` are scratch registers. -/
@[ext] structure Control (k : ℕ) (State : Type) where
  /-- The source state, or `none` when its final action has executed. -/
  state : Option State
  /-- Whether the bounded input head is at the blank before the word. -/
  atLeft : Bool
  /-- The current cell on each work tape. -/
  head : Fin k → Option Bool
  /-- A scratch register for input movement and output reversal. -/
  symbol : Option Bool
  /-- Whether the current cleanup round found a nonempty auxiliary stack. -/
  busy : Bool
  deriving Fintype

/-- Initial finite control, also restored before halting. -/
def initialControl (q : State) : Control k State :=
  ⟨some q, false, fun _ => none, none, false⟩

/-- A statement over the compiler's stack alphabets, phases and finite control. -/
abbrev Statement (k : ℕ) (State : Type) :=
  TM2.Stmt (Alphabet (k := k)) Label (Control k State)

open TM2.Stmt

/-- Write the current work cell, retaining the old value when no write is requested. -/
def writeWork (i : Fin k) (write : Option (Option Bool)) (next : Statement k State) :
    Statement k State :=
  load (fun v => { v with head := Function.update v.head i (write.getD (v.head i)) }) next

/-- Moving a work head transfers its old current cell to the opposite stack. -/
def moveWork (i : Fin k) (direction : SignType) (next : Statement k State) :
    Statement k State :=
  match direction with
  | .zero => next
  | .neg => push (.work i true) (fun v => v.head i)
      (pop (.work i false) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)
  | .pos => push (.work i false) (fun v => v.head i)
      (pop (.work i true) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)

/-- A fixed native work-tape action is a bounded straight-line stack statement. -/
def workAction (i : Fin k) (action : Option (Option Bool) × SignType)
    (next : Statement k State) : Statement k State :=
  writeWork i action.1 (moveWork i action.2 next)

/-- Move the bounded read-only input head. Empty stacks detect the two boundaries. -/
def moveInput (direction : SignType) (next : Statement k State) : Statement k State :=
  match direction with
  | .zero => next
  | .neg => TM2.Stmt.branch (fun v => v.atLeft) next
      (pop .before (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .input (fun v => v.symbol.getD false) next)
          (load (fun v => { v with atLeft := true }) next)))
  | .pos => TM2.Stmt.branch (fun v => v.atLeft) (load (fun v => { v with atLeft := false }) next)
      (pop .input (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .before (fun v => v.symbol.getD false) next) next))

/-- A source step updates every work tape, the input head, output and control. -/
def action (a : Turing.Action k Bool State) : Statement k State :=
  (List.finRange k).foldr (fun i next => workAction i (a.workTapes i) next)
    (moveInput a.inputTape
      (a.output.elim id (fun b => push .reversed (fun _ => b))
        (load (fun v => { v with state := a.state, symbol := none, busy := false })
          (goto (fun _ => .run)))))

/-- Stacks discarded before output reversal. -/
def auxiliaries (k : ℕ) : List (Stack k) :=
  [.input, .before] ++ (List.finRange k).flatMap (fun i => [.work i false, .work i true])

/-- Discard one cell from each auxiliary stack and remember whether any was nonempty. -/
def discard (s : Stack k) (next : Statement k State) : Statement k State :=
  pop s (fun v a => { v with busy := v.busy || a.isSome }) next

/-- A cleanup round either reduces auxiliary storage or advances to output reversal. -/
def clean : Statement k State :=
  load (fun v => { v with busy := false })
    ((auxiliaries k).foldr discard
      (TM2.Stmt.branch (fun v => v.busy) (goto (fun _ => .clean)) (goto (fun _ => .reverse))))

/-- The fixed program has finite control and a finite alphabet on every stack. -/
def program [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    Label → Statement k State
  | .run => peek .input (fun v a => { v with symbol := a })
      (TM2.select fun v => match v.state with
        | none => goto (fun _ => .clean)
        | some q => action (transition q (if v.atLeft then none else v.symbol) v.head))
  | .clean => clean
  | .reverse => pop .reversed (fun v a => { v with symbol := a })
      (TM2.Stmt.branch (fun v => v.symbol.isSome)
        (push .output (fun v => v.symbol.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => initialControl q₀) halt))

/-- The actual Mathlib `FinTM2` produced by the reverse compiler. -/
abbrev machine [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    FinTM2 where
  K := Stack k
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .run
  σ := Control k State
  initialState := initialControl q₀
  m := program q₀ transition

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Raw configurations for the multi-tape to TM2 compiler

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Data`: finite stacks representing a binary native configuration.
* `Turing.MultiTapeTM.ToTM2.Data.step`: apply one native action to the raw configuration.
* `Turing.MultiTapeTM.ToTM2.Data.run`: execute a native machine with raw stacks.
* `Turing.MultiTapeTM.ToTM2.Data.Represents`: agreement with a native configuration.

## Main results

* `Turing.MultiTapeTM.ToTM2.Data.represents_run`: raw execution agrees with native execution.
* `Turing.MultiTapeTM.ToTM2.Data.input_length_run`: input storage is exactly the input length.
* `Turing.MultiTapeTM.ToTM2.Data.output_prefix_run`: chronological output grows by extension.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A native binary configuration stored as finite stacks, with chronological output. -/
@[ext]
structure Data (k : ℕ) (State : Type) where
  /-- The current state, or `none` after halting. -/
  state : Option State
  /-- The bounded read-only input zipper. -/
  input : Input Bool
  /-- The work tapes, retaining all visited cells. -/
  work : Fin k → RawTape Bool
  /-- Symbols emitted so far, in chronological order. -/
  output : List Bool

namespace Data

variable {k : ℕ} {State : Type}

/-- Initialize the input zipper and blank work tapes. -/
def init (q₀ : State) (input : List Bool) : Data k State :=
  ⟨some q₀, Input.init input, fun _ => RawTape.init, []⟩

/-- Apply an action, including the output and movement of its final halting step. -/
def step (d : Data k State) (a : Action k Bool State) : Data k State where
  state := a.state
  input := d.input.move a.inputTape
  work i := (d.work i).step (a.workTapes i)
  output := d.output ++ a.output.toList

/-- Select and apply the native transition, staying put once halted. -/
noncomputable def totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) : Data k State :=
  match d.state with
  | none => d
  | some q => d.step (tm.tr q d.input.read (fun i => (d.work i).head))

/-- Execute a fixed number of total steps from an arbitrary raw configuration. -/
noncomputable def runFrom (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    Data k State :=
  (totalStep tm)^[t] d

/-- Execute a fixed number of total steps from the initial raw configuration. -/
noncomputable def run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    Data k State :=
  runFrom tm (init tm.q₀ input) t

/-- Raw fields agree with the corresponding native state, heads, tapes and output. -/
structure Represents (d : Data k State) {sourceInput : List Bool}
    (cfg : Cfg k Bool State sourceInput) : Prop where
  /-- The control states agree. -/
  state : d.state = cfg.state
  /-- The input zipper represents the native bounded head. -/
  input : d.input.Represents sourceInput cfg.inputPos
  /-- Each work tape represents its native integer-indexed tape and head. -/
  work : ∀ i, (d.work i).Represents (cfg.workTapes i) (cfg.workTapePos i)
  /-- Output is chronological in both representations. -/
  output : d.output = cfg.output

@[simp]
theorem runFrom_zero (tm : MultiTapeTM k Bool State) (d : Data k State) :
    runFrom tm d 0 = d := by rfl

/-- The next raw configuration is one total step from the preceding configuration. -/
theorem runFrom_succ (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    runFrom tm d (t + 1) = totalStep tm (runFrom tm d t) := by
  exact Function.iterate_succ_apply' _ _ _

@[simp]
theorem run_zero (tm : MultiTapeTM k Bool State) (input : List Bool) :
    run tm input 0 = init tm.q₀ input := by rfl

/-- The next raw configuration on an input is obtained by one total step. -/
theorem run_succ (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    run tm input (t + 1) = totalStep tm (run tm input t) := by
  exact runFrom_succ _ _ _

/-- Halted raw configurations are fixed by the total step. -/
theorem totalStep_of_halt (tm : MultiTapeTM k Bool State) {d : Data k State}
    (h : d.state = none) : totalStep tm d = d := by
  rw [totalStep, h]

/-- A live raw configuration applies the transition selected from its current reads. -/
theorem totalStep_of_state (tm : MultiTapeTM k Bool State) {d : Data k State} {q : State}
    (h : d.state = some q) :
    totalStep tm d = d.step (tm.tr q d.input.read (fun i => (d.work i).head)) := by
  rw [totalStep, h]

namespace Represents

variable {d : Data k State} {sourceInput : List Bool} {cfg : Cfg k Bool State sourceInput}

/-- Initialization represents the native initial configuration. -/
theorem init (q₀ : State) (input : List Bool) :
    (Data.init (k := k) q₀ input).Represents (Cfg.init q₀ input) :=
  ⟨rfl, Input.represents_init input, fun _ => RawTape.Represents.init, rfl⟩

/-- Applying the same action preserves every field of the representation. -/
theorem step (h : d.Represents cfg) (a : Action k Bool State) :
    (d.step a).Represents (a.apply cfg) :=
  ⟨rfl, h.input.move a.inputTape, fun i => (h.work i).step (a.workTapes i),
    congrArg (· ++ a.output.toList) h.output⟩

/-- Raw and native configurations select the same action and take corresponding total steps. -/
theorem totalStep (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) :
    (Data.totalStep tm d).Represents (tm.step cfg) := by
  cases hs : d.state with
  | none =>
    rw [Data.totalStep_of_halt tm hs, tm.step_of_halt (h.state.symm.trans hs)]
    exact h
  | some q =>
    rw [Data.totalStep_of_state tm hs, tm.step_of_state (h.state.symm.trans hs)]
    have hi : d.input.read = cfg.inputSymbol := h.input.read_eq_inputSymbol
    have hw : (fun i => (d.work i).head) = cfg.workTapeSymbols :=
      funext fun i => (h.work i).head
    rw [hi, hw]
    exact h.step _

/-- Any number of raw total steps represents the same number of native total steps. -/
theorem runFrom (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) (t : ℕ) :
    (Data.runFrom tm d t).Represents (tm.runFrom cfg t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Data.runFrom_succ, MultiTapeTM.runFrom, Function.iterate_succ_apply',
      ← MultiTapeTM.runFrom]
    exact ih.totalStep tm

end Represents

/-- Raw execution from initialization agrees with the native execution, even after halting. -/
theorem represents_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).Represents (tm.runFrom (tm.initCfg input) t) :=
  (Represents.init tm.q₀ input).runFrom tm t

/-- At every time, the raw input stacks retain exactly the original input length. -/
theorem input_length_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).input.left.length + (run tm input t).input.right.length = input.length :=
  (represents_run tm input t).input.length_eq

/-- The raw output is exactly the native chronological output. -/
theorem output_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).output = (tm.runFrom (tm.initCfg input) t).output :=
  (represents_run tm input t).output

/-- The raw control state agrees with the native state at every time. -/
theorem state_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).state = (tm.runFrom (tm.initCfg input) t).state :=
  (represents_run tm input t).state

/-- Each action only appends to the output. -/
theorem output_prefix_step (d : Data k State) (a : Action k Bool State) :
    d.output <+: (d.step a).output :=
  ⟨a.output.toList, rfl⟩

/-- Total steps only append to the output, including a step which halts. -/
theorem output_prefix_totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) :
    d.output <+: (totalStep tm d).output := by
  cases hs : d.state with
  | none => rw [totalStep_of_halt tm hs]
  | some q => rw [totalStep_of_state tm hs]; exact output_prefix_step _ _

/-- Earlier raw outputs are prefixes of all later raw outputs. -/
theorem output_prefix_run (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t u : ℕ} (h : t ≤ u) : (run tm input t).output <+: (run tm input u).output := by
  induction u, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ u _ ih =>
    rw [run_succ]
    exact ih.trans (output_prefix_totalStep tm _)

/-- The amount of output never decreases. -/
theorem output_length_run_mono (tm : MultiTapeTM k Bool State) (input : List Bool) :
    Monotone (fun t => (run tm input t).output.length) :=
  fun _ _ h => (output_prefix_run tm input h).length_le

/-- Raw execution stays at its final configuration after halting. -/
theorem run_eq_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool) {t u : ℕ}
    (hle : t ≤ u) (hhalt : (run tm input t).state = none) :
    run tm input u = run tm input t := by
  induction u, hle using Nat.le_induction with
  | base => rfl
  | succ u _ ih => rw [run_succ, ih, totalStep_of_halt tm hhalt]

/-- Every intermediate output is bounded by the output of a terminating run. -/
theorem output_length_run_le_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (hhalt : (run tm input t).state = none) (u : ℕ) :
    (run tm input u).output.length ≤ (run tm input t).output.length := by
  rcases le_total u t with h | h
  · exact output_length_run_mono tm input h
  · rw [run_eq_of_halt tm input h hhalt]

/-- Every raw output is a prefix of the complete output of a terminating native computation. -/
theorem output_prefix_run_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output <+: output := by
  obtain ⟨u, hhalt, hout⟩ := h
  have hraw : (run tm input u).output = output := (output_run tm input u).trans hout
  rcases le_total t u with h | h
  · exact hraw ▸ output_prefix_run tm input h
  · rw [run_eq_of_halt tm input h ((state_run tm input u).trans hhalt), hraw]

/-- A terminating native output bounds every intermediate raw output, without a time term. -/
theorem output_length_run_le_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output.length ≤ output.length :=
  (output_prefix_run_of_computes h t).length_le

end Data
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Stack representation for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.encode`: represent a raw configuration at a source-step boundary.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Finite control corresponding to raw simulation data, with arbitrary scratch registers. -/
def control (d : Data k State) (symbol : Option Bool := none) (busy : Bool := false) :
    Control k State := ⟨d.state, d.input.atLeft, fun i => (d.work i).head, symbol, busy⟩

/-- The stack representation keeps output in reverse order until cleanup. -/
def store (d : Data k State) : (s : Stack k) → List (Alphabet s)
  | .input => d.input.right
  | .before => d.input.left
  | .output => []
  | .reversed => d.output.reverse
  | .work i false => (d.work i).left
  | .work i true => (d.work i).right

/-- The TM2 configuration at a source-step boundary. -/
def encode (d : Data k State) : TM2.Cfg (Alphabet (k := k)) Label (Control k State) :=
  ⟨some .run, control d, store d⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Compiled input movement and output emission

## Main definitions

* `Turing.MultiTapeTM.ToTM2.inputSymbol`: the scratch symbol after compiled input movement.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_moveInput`: compiled movement agrees with the raw input
  zipper, without a validity assumption.
* `Turing.MultiTapeTM.ToTM2.stepAux_finish`: emit an optional bit and restore boundary control.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Input movement retains scratch at the left boundary and otherwise remembers the popped bit. -/
def inputSymbol (d : Data k State) (direction : SignType) (scratch : Option Bool) : Option Bool :=
  if d.input.atLeft then scratch else
    match direction with
    | .zero => scratch
    | .neg => d.input.left.head?
    | .pos => d.input.right.head?

/-- The compiled input movement agrees with the zipper on every raw configuration. -/
theorem stepAux_moveInput (d : Data k State) (direction : SignType)
    (next : Statement k State) (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux (moveInput direction next) (control d scratch busy) (store d) =
      TM2.stepAux next
        (control { d with input := d.input.move direction } (inputSymbol d direction scratch) busy)
        (store { d with input := d.input.move direction }) := by
  classical
  rcases d with ⟨state, ⟨left, right, atLeft⟩, work, output⟩
  cases direction <;> cases atLeft
  all_goals try rfl
  all_goals cases left <;> cases right
  all_goals
    simp only [moveInput, TM2.stepAux, control, store, inputSymbol, Input.move, Input.moveLeft,
      Input.moveRight]
  all_goals simp only [Alphabet, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.isSome_none, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  all_goals
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

/-- Emitting an optional bit and loading the next source state restores a step boundary. -/
theorem stepAux_finish (d : Data k State) (state : Option State) (output : Option Bool)
    (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux
      (output.elim id (fun b => TM2.Stmt.push .reversed (fun _ => b))
        (TM2.Stmt.load (fun v => { v with state := state, symbol := none, busy := false })
          (TM2.Stmt.goto (fun _ => .run))))
      (control d scratch busy) (store d) =
      encode { d with state := state, output := d.output ++ output.toList } := by
  classical
  cases output with
  | none =>
    simp only [Option.elim, encode, Option.toList_none, List.append_nil]
    congr 1
  | some b =>
    simp only [Option.elim, TM2.stepAux, encode, Option.toList_some]
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Execution correspondence for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_action`: a compiled action realizes the raw tape update.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private theorem control_write (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with
      head := (Function.update (control d symbol busy).head i
        (w.getD ((control d symbol busy).head i))) }
      = control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i <;> simp [Function.update, control, RawTape.write, h]

private theorem store_write (d : Data k State) (i : Fin k) (w : Option (Option Bool)) :
    store { d with work := Function.update d.work i ((d.work i).write w) } = store d := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i <;> cases side <;> simp [store, RawTape.write, h]
  | _ => rfl

private theorem stepAux_writeWork (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (writeWork i w next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).write w) }) := by
  simp only [writeWork, TM2.stepAux, control_write, store_write]

private theorem control_moveLeft (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i false)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveLeft } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveLeft (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
      (.work i false) (d.work i).left.tail =
      store { d with work := Function.update d.work i (d.work i).moveLeft } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveLeft]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem control_moveRight (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i true)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveRight } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveRight (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
      (.work i true) (d.work i).right.tail =
      store { d with work := Function.update d.work i (d.work i).moveRight } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveRight]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem stepAux_moveWork (d : Data k State) (i : Fin k) (direction : SignType)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (moveWork i direction next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step (none, direction)) }
          symbol busy)
        (store
          { d with work := Function.update d.work i ((d.work i).step (none, direction)) }) := by
  cases direction with
  | zero => simp [moveWork, RawTape.step, RawTape.write, Function.update_eq_self]
  | neg =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i false ≠ Stack.work i true)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i false)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
        (.work i false) (d.work i).left.tail) = _
    rw [control_moveLeft, store_moveLeft]
    rfl
  | pos =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i true ≠ Stack.work i false)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i true)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
        (.work i true) (d.work i).right.tail) = _
    rw [control_moveRight, store_moveRight]
    rfl

private theorem stepAux_workAction (d : Data k State) (i : Fin k)
    (a : Option (Option Bool) × SignType) (next : Statement k State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (workAction i a next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step a) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).step a) }) := by
  rw [workAction, stepAux_writeWork, stepAux_moveWork]
  cases a with | mk w direction =>
    cases direction <;> simp [RawTape.step, RawTape.write, Function.update_idem]

private def applyWorks (d : Data k State)
    (a : Fin k → Option (Option Bool) × SignType) (indices : List (Fin k)) : Data k State :=
  indices.foldl (fun d i => { d with work := Function.update d.work i ((d.work i).step (a i)) }) d

private theorem stepAux_workActions (indices : List (Fin k))
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (indices.foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control (applyWorks d a indices) symbol busy)
        (store (applyWorks d a indices)) := by
  induction indices generalizing d with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldr_cons, stepAux_workAction, ih]
    rfl

private theorem applyWorks_eq (indices : List (Fin k)) (h : indices.Nodup)
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State) :
    applyWorks d a indices =
      { d with work := fun i => if i ∈ indices then (d.work i).step (a i) else d.work i } := by
  induction indices generalizing d with
  | nil => simp [applyWorks]
  | cons i indices ih =>
    rw [List.nodup_cons] at h
    change applyWorks { d with work := Function.update d.work i ((d.work i).step (a i)) }
      a indices = _
    rw [ih h.2]
    apply Data.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst j
      simp [h.1]
    · by_cases hmem : j ∈ indices <;> simp [hj, hmem]

/-- Each work tape is updated once, in a fixed straight-line statement. -/
private theorem stepAux_allWork (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux ((List.finRange k).foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control { d with work := fun i => (d.work i).step (a i) } symbol busy)
        (store { d with work := fun i => (d.work i).step (a i) }) := by
  rw [stepAux_workActions, applyWorks_eq _ (List.nodup_finRange k)]
  simp only [List.mem_finRange, ↓reduceIte]

/-- One complete compiled action realizes the native update on finite tape data. -/
theorem stepAux_action (d : Data k State) (a : Turing.Action k Bool State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (action a) (control d symbol busy) (store d) = encode (d.step a) := by
  rw [action, stepAux_allWork, stepAux_moveInput, stepAux_finish]
  rfl

/-- One live source transition is exactly one Mathlib stack-machine transition. -/
theorem step_encode [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.step (program tm.q₀ tm.tr) (encode d) = some (encode (Data.totalStep tm d)) := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  change some (TM2.stepAux
    (match d.state with
    | none => TM2.Stmt.goto (fun _ => .clean)
    | some q => action (tm.tr q (if d.input.atLeft then none else d.input.right.head?)
        (fun i => (d.work i).head)))
    (control d d.input.right.head? false) (store d)) = _
  rw [hq, stepAux_action, Data.totalStep_of_state tm hq]
  rfl

/-- A halted source starts cleanup on the following target step. -/
theorem step_encode_halt [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.step (program tm.q₀ tm.tr) (encode d) =
      some ⟨some .clean, control d d.input.right.head? false, store d⟩ := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  simp only [control, hq, TM2.stepAux, store]

/-- Native initialization already has the stack layout required by the compiler. -/
theorem encode_init [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool) :
    encode (Data.init tm.q₀ input) = initList (machine tm.q₀ tm.tr) input := by
  apply congrArg (fun s =>
    (⟨some .run, initialControl tm.q₀, s⟩ : TM2.Cfg (Alphabet (k := k)) Label (Control k State)))
  funext s
  cases s with
  | work i b => cases b <;> rfl
  | _ => rfl

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Whole-run correspondence before cleanup

The compiler executes exactly one source transition per TM2 transition until the first halting
source configuration. Its next transition enters cleanup. These statements include the final
source action, which may write, move heads and emit a bit while halting.

## Main results

* `Turing.MultiTapeTM.ToTM2.iterate_encode`: correspondence of every source execution prefix.
* `Turing.MultiTapeTM.ToTM2.prefixEvals`: the same correspondence with Mathlib's partial clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type} [Fintype State]

private theorem stepTotal_encode (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) = encode (Data.totalStep tm d) :=
  Option.some.inj (step_encode tm d hq)

theorem stepTotal_encode_halt (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) =
      ⟨some .clean, control d d.input.right.head? false, store d⟩ :=
  Option.some.inj (step_encode_halt tm d hq)

/-- Every source prefix through the first halted configuration is reproduced exactly. -/
theorem iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input) =
      encode (Data.run tm input i) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact (encode_init tm input).symm
  | succ i ih =>
    have hstep :
        (TM2.stepTotal (program tm.q₀ tm.tr))^[i + 1] (initList (machine tm.q₀ tm.tr) input) =
          TM2.stepTotal (program tm.q₀ tm.tr)
            ((TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input)) :=
      Function.iterate_succ_apply' _ i _
    rw [hstep, ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q => rw [stepTotal_encode tm _ hq, Data.run_succ]

/-- The partial clock retains a successor throughout each source execution prefix. -/
private theorem partial_iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (fun c => c.bind (machine tm.q₀ tm.tr).step)^[i]
      (some (initList (machine tm.q₀ tm.tr) input)) = some (encode (Data.run tm input i)) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact congrArg some (encode_init tm input).symm
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q =>
      change TM2.step (program tm.q₀ tm.tr) (encode (Data.run tm input i)) = _
      rw [step_encode tm _ hq, Data.run_succ]

/-- Mathlib's partial execution reaches each source prefix in exactly that many transitions. -/
def prefixEvals (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step
      (initList (machine tm.q₀ tm.tr) input) (some (encode (Data.run tm input i))) i :=
  ⟨⟨i, partial_iterate_encode tm input ht hi⟩, le_rfl⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Canonical cleanup for the multi-tape to TM2 compiler

Cleanup discards the input and work stacks, reverses the accumulated output onto the output
stack, and resets finite control. Existing output is retained as a suffix.

## Main definitions

* `StateTransition.EvalsToInTime.cons`, `.mono`: prepend one transition or enlarge the
  clock of a bounded partial execution.
* `Turing.MultiTapeTM.ToTM2.auxiliaryLength`: storage discarded by cleanup.
* `Turing.MultiTapeTM.ToTM2.totalStackLength`: storage on all stacks, including input and output.

## Main results

* `Turing.MultiTapeTM.ToTM2.cleanupEvals`: canonical halting with an explicit linear clock.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace StateTransition.EvalsToInTime

/-- Prepend one transition to a bounded execution. -/
def cons {α : Type} {f : α → Option α} {a b c : α} {n : ℕ}
    (hs : f a = some b) (h : EvalsToInTime f b (some c) n) :
    EvalsToInTime f a (some c) (n + 1) where
  steps := h.steps + 1
  evals_in_steps := by
    rw [Function.iterate_succ_apply]
    change (flip bind f)^[h.steps] (f a) = some c
    rw [hs]
    exact h.evals_in_steps
  steps_le_m := Nat.add_le_add_right h.steps_le_m 1

/-- Increase the clock of a bounded execution. -/
def mono {α : Type} {f : α → Option α} {a c : α} {m n : ℕ}
    (h : EvalsToInTime f a (some c) m) (hmn : m ≤ n) :
    EvalsToInTime f a (some c) n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

end StateTransition.EvalsToInTime

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Exactly the stacks other than the two output stacks are discarded. -/
@[simp] theorem mem_auxiliaries (s : Stack k) :
    s ∈ auxiliaries k ↔ s ≠ .output ∧ s ≠ .reversed := by
  cases s with
  | work i b => cases b <;> simp [auxiliaries]
  | _ => simp [auxiliaries]

/-- Each auxiliary is popped exactly once in a cleanup round. -/
theorem auxiliaries_nodup (k : ℕ) : (auxiliaries k).Nodup := by
  have hp : List.Pairwise (Function.onFun List.Disjoint
      (fun i : Fin k => [Stack.work i false, Stack.work i true])) (List.finRange k) := by
    apply (List.nodup_finRange k).imp
    intro i j hij
    simp [Function.onFun, List.disjoint_left, hij]
  simpa [auxiliaries, List.nodup_append, List.nodup_flatMap, List.disjoint_left] using hp

/-- Pop each named stack once; the list is assumed duplicate-free when used operationally. -/
private def poppedStore (ss : List (Stack k)) (store : ∀ s : Stack k, List (Alphabet s)) :
    ∀ s : Stack k, List (Alphabet s) :=
  fun s => if s ∈ ss then (store s).tail else store s

private theorem poppedStore_cons (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    poppedStore ss (Function.update store s (store s).tail) = poppedStore (s :: ss) store := by
  funext t
  by_cases ht : t = s
  · subst t
    simp [poppedStore, h]
  · simp [poppedStore, ht]

private theorem any_update (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    ss.any (fun t => ((Function.update store s (store s).tail) t).head?.isSome) =
      ss.any (fun t => (store t).head?.isSome) := by
  induction ss with
  | nil => rfl
  | cons t ss ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.any_cons, Function.update_of_ne (Ne.symm h.1), ih h.2]

/-- The straight-line discard statement records whether a stack was nonempty before popping. -/
private theorem stepAux_discard (ss : List (Stack k)) (hss : ss.Nodup)
    (next : Statement k State) (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (ss.foldr discard next) v store =
      TM2.stepAux next
        { v with busy := v.busy || ss.any (fun s => (store s).head?.isSome) }
        (poppedStore ss store) := by
  induction ss generalizing v store with
  | nil =>
    have hs : poppedStore [] store = store := by funext s; simp [poppedStore]
    simp only [List.foldr_nil, List.any_nil, Bool.or_false, hs]
  | cons s ss ih =>
    rw [List.nodup_cons] at hss
    simp only [List.foldr_cons, discard, TM2.stepAux]
    rw [ih hss.2, poppedStore_cons s ss store hss.1, any_update s ss store hss.1]
    simp [Bool.or_assoc]

/-- Total auxiliary storage before a cleanup round. -/
def auxiliaryLength (store : ∀ s : Stack k, List (Alphabet s)) : ℕ :=
  ∑ s : Stack k, if s ∈ auxiliaries k then (store s).length else 0

/-- Total stack storage, counting both output stacks and all auxiliary stacks. -/
def totalStackLength (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) : ℕ :=
  ∑ s : Stack k, (cfg.stk s).length

/-- Every stack contributes exactly once to the storage accounting. -/
theorem totalStackLength_eq (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) :
    totalStackLength cfg = auxiliaryLength cfg.stk +
      (cfg.stk .reversed).length + (cfg.stk .output).length := by
  classical
  calc
    _ = ∑ s : Stack k, ((if s ∈ auxiliaries k then (cfg.stk s).length else 0) +
        (if s = .reversed then (cfg.stk s).length else 0) +
        (if s = .output then (cfg.stk s).length else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases s <;> simp
    _ = _ := by simp [auxiliaryLength, Finset.sum_add_distrib]

/-- Whether a cleanup round encounters a nonempty auxiliary stack. -/
private def auxiliaryBusy (store : ∀ s : Stack k, List (Alphabet s)) : Bool :=
  (auxiliaries k).any (fun s => (store s).head?.isSome)

/-- A round pops all auxiliaries, preserving both output stacks. -/
private theorem stepAux_clean (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux clean v store =
      ⟨some (if auxiliaryBusy store then .clean else .reverse),
        { v with busy := auxiliaryBusy store }, poppedStore (auxiliaries k) store⟩ := by
  simp only [clean, TM2.stepAux]
  rw [stepAux_discard _ (auxiliaries_nodup k)]
  simp only [Bool.false_or, TM2.stepAux]
  simp only [auxiliaryBusy]
  by_cases hb : (auxiliaries k).any (fun s => (store s).head?.isSome) = true
  · simp only [hb, Bool.cond_true, ↓reduceIte]
  · have hf := Bool.eq_false_iff.mpr hb
    simp only [hf, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]

/-- No auxiliary is busy precisely when all of them are empty. -/
private theorem auxiliaryBusy_eq_false_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryBusy store = false ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryBusy, List.any_eq_false]

/-- Zero auxiliary storage is equivalent to emptiness of every auxiliary stack. -/
theorem auxiliaryLength_eq_zero_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength store = 0 ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryLength, Finset.sum_eq_zero_iff]

/-- Popping auxiliary stacks cannot increase their total length. -/
private theorem auxiliaryLength_popped_le (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength (poppedStore (auxiliaries k) store) ≤ auxiliaryLength store := by
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : s ∈ auxiliaries k
  · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
    exact Nat.sub_le _ _
  · simp [h]

/-- A busy round strictly decreases auxiliary storage. -/
private theorem auxiliaryLength_popped_lt (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = true) :
    auxiliaryLength (poppedStore (auxiliaries k) store) < auxiliaryLength store := by
  have hex : ∃ s, s ∈ auxiliaries k ∧ store s ≠ [] := by
    by_contra! h
    have := (auxiliaryBusy_eq_false_iff store).2 h
    simp [hb] at this
  obtain ⟨s, hs, hne⟩ := hex
  apply Finset.sum_lt_sum
  · intro t ht
    by_cases h : t ∈ auxiliaries k
    · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
      exact Nat.sub_le _ _
    · simp [h]
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    simp only [poppedStore, hs, ↓reduceIte, List.length_tail]
    have : 0 < (store s).length := List.length_pos_iff.mpr hne
    omega

/-- A quiet round leaves every stack unchanged. -/
private theorem poppedStore_eq_of_not_busy (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = false) : poppedStore (auxiliaries k) store = store := by
  funext s
  by_cases h : s ∈ auxiliaries k
  · simp [poppedStore, h, (auxiliaryBusy_eq_false_iff store).mp hb s h]
  · simp [poppedStore, h]

variable [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)

/-- Reversal transfers one symbol, or resets finite control and halts on the empty stack. -/
private theorem stepAux_reverse (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      match store .reversed with
      | [] => ⟨none, initialControl q₀, Function.update store .reversed []⟩
      | b :: bs => ⟨some .reverse, { v with symbol := some b },
          Function.update (Function.update store .reversed bs) .output (b :: store .output)⟩ := by
  cases h : store .reversed with
  | nil => simp [program, TM2.stepAux, h, Option.isSome, Option.getD]
  | cons b bs =>
    simp only [program, TM2.stepAux, h, List.head?_cons, List.tail_cons,
      Option.isSome, Bool.cond_true]
    rfl

/-- When the auxiliaries are empty, the last reversal step has the canonical halting shape. -/
private theorem stepAux_reverse_nil (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) (hr : store .reversed = []) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      haltList (machine q₀ transition) (store .output) := by
  rw [stepAux_reverse, hr]
  change TM2.Cfg.mk none (initialControl q₀) _ = TM2.Cfg.mk none (initialControl q₀) _
  congr 1
  funext s
  cases s with
  | input => simp [machine, ha .input (by simp)]
  | before => simp [machine, ha .before (by simp)]
  | output => rfl
  | reversed => simp [machine]
  | work i b => simp [machine, ha (.work i b) (by simp)]

/-- Reversal preserves already populated output, which becomes a suffix of the final word. -/
private def reverseEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .reverse, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      ((store .reversed).length + 1) := by
  cases hr : store .reversed with
  | nil =>
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some (haltList (machine q₀ transition) (store .output)) := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      exact congrArg some (stepAux_reverse_nil q₀ transition v store ha hr)
    change StateTransition.EvalsToInTime _ _
      (some (haltList (machine q₀ transition) (store .output))) 1
    exact .cons hs (.refl _ _)
  | cons b bs =>
    let store' := Function.update (Function.update store .reversed bs) .output (b :: store .output)
    have ha' : ∀ s ∈ auxiliaries k, store' s = [] := by
      intro s hs
      have hne := (mem_auxiliaries s).mp hs
      simpa only [store', Function.update_of_ne hne.1, Function.update_of_ne hne.2] using ha s hs
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some ⟨some .reverse, { v with symbol := some b }, store'⟩ := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      rw [stepAux_reverse, hr]
    have hrec := reverseEvals { v with symbol := some b } store' ha'
    have hrev : store' .reversed = bs := by simp [store']
    have hout : store' .output = b :: store .output := by
      dsimp only [store']
      exact Function.update_self _ _ _
    rw [hrev, hout] at hrec
    rw [List.reverse_cons]
    have hw : List.append (α := Bool) (bs.reverse ++ [b]) (store .output) =
        List.append (α := Bool) bs.reverse (b :: store .output) :=
      List.append_assoc (α := Bool) bs.reverse [b] (store .output)
    rw [hw]
    change StateTransition.EvalsToInTime _ _ _ (bs.length + 1 + 1)
    exact .cons hs hrec
termination_by (store .reversed).length
decreasing_by simp_wf; rw [hr]; exact Nat.lt_succ_self _

/-- Cleanup reaches the canonical halting configuration within a linear number of TM2 steps. -/
private def cleanEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .clean, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      (auxiliaryLength store + (store .reversed).length + 2) := by
  cases hb : auxiliaryBusy store with
  | false =>
    have ha := (auxiliaryBusy_eq_false_iff store).mp hb
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .reverse, { v with busy := false }, store⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb, poppedStore_eq_of_not_busy store hb]
      rfl
    exact (StateTransition.EvalsToInTime.cons hs (reverseEvals q₀ transition _ store ha)).mono
      (by omega)
  | true =>
    let store' := poppedStore (auxiliaries k) store
    have hrev : store' .reversed = store .reversed := by simp [store', poppedStore]
    have hout : store' .output = store .output := by simp [store', poppedStore]
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .clean, { v with busy := true }, store'⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb]
      rfl
    have hrec := cleanEvals { v with busy := true } store'
    rw [hrev, hout] at hrec
    have hlt := auxiliaryLength_popped_lt store hb
    exact (StateTransition.EvalsToInTime.cons hs hrec).mono (by dsimp only [store'] at *; omega)
termination_by auxiliaryLength store
decreasing_by exact auxiliaryLength_popped_lt store hb

/-- Configuration form of `cleanEvals`, allowing arbitrary finite control and stack contents. -/
def cleanupEvals (cfg : (machine q₀ transition).Cfg) (hl : cfg.l = some .clean) :
    StateTransition.EvalsToInTime (machine q₀ transition).step cfg
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (cfg.stk .reversed).reverse (cfg.stk .output))))
      (auxiliaryLength cfg.stk + (cfg.stk .reversed).length + 2) := by
  cases cfg with | mk l v store =>
    cases hl
    exact cleanEvals q₀ transition v store

end
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Resource bounds for the reverse TM2 compiler

Input storage and the output buffer count toward the target clock. Each source step adds at most
one symbol to the work storage of each simulated tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.outputsInTime`: output correspondence with a linear simulation clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private def stackEquiv (k : ℕ) : Stack k ≃ ((Bool ⊕ Bool) ⊕ Fin k × Bool) where
  toFun
    | .input => .inl (.inl false)
    | .before => .inl (.inl true)
    | .output => .inl (.inr false)
    | .reversed => .inl (.inr true)
    | .work i b => .inr (i, b)
  invFun
    | .inl (.inl false) => .input
    | .inl (.inl true) => .before
    | .inl (.inr false) => .output
    | .inl (.inr true) => .reversed
    | .inr (i, b) => .work i b
  left_inv s := by cases s with | work i b => cases b <;> rfl | _ => rfl
  right_inv s := by
    rcases s with ((b | b) | ⟨i, b⟩) <;> cases b <;> rfl

private theorem sum_stack (f : Stack k → ℕ) :
    ∑ s, f s = f .input + f .before + f .output + f .reversed +
      ∑ i, (f (.work i false) + f (.work i true)) := by
  rw [← (stackEquiv k).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, stackEquiv,
    Equiv.symm_mk, Equiv.coe_fn_mk]
  simp [add_comm, add_assoc]

/-- Stack storage at a source-step boundary, including the input and output. -/
private theorem totalStackLength_encode (d : Data k State) :
    totalStackLength (encode d) = d.input.left.length + d.input.right.length +
      (∑ i, ((d.work i).left.length + (d.work i).right.length)) + d.output.length := by
  rw [totalStackLength, sum_stack]
  simp only [encode, store, List.length_nil, List.length_reverse]
  omega

/-- Auxiliary storage excludes the accumulated output. -/
private theorem auxiliaryLength_store (d : Data k State) :
    auxiliaryLength (store d) = d.input.left.length + d.input.right.length +
      ∑ i, ((d.work i).left.length + (d.work i).right.length) := by
  have h := totalStackLength_encode d
  rw [totalStackLength_eq] at h
  simp only [encode, store, List.length_reverse, List.length_nil, Nat.add_zero] at h
  omega

private theorem auxiliaryLength_run_time_le (tm : MultiTapeTM k Bool State)
    (input : List Bool) (t : ℕ) :
    auxiliaryLength (store (Data.run tm input t)) ≤ input.length + k * (t + 1) := by
  rw [auxiliaryLength_store, Data.input_length_run]
  have hlocal (i : Fin k) : ((Data.run tm input t).work i).left.length +
      ((Data.run tm input t).work i).right.length ≤ t := by
    induction t with
    | zero => simp [Data.run_zero, Data.init, RawTape.init]
    | succ t ih =>
      rw [Data.run_succ]
      let q := Data.run tm input t
      change ((Data.totalStep tm q).work i).left.length +
        ((Data.totalStep tm q).work i).right.length ≤ t + 1
      cases hs : q.state with
      | none =>
        rw [Data.totalStep_of_halt tm hs]
        exact ih.trans (Nat.le_succ t)
      | some st =>
        rw [Data.totalStep_of_state tm hs]
        let a := tm.tr st q.input.read (fun i => (q.work i).head)
        have h := RawTape.span_step_le (q.work i) (a.workTapes i)
        change ((q.work i).step (a.workTapes i)).left.length +
          ((q.work i).step (a.workTapes i)).right.length ≤ t+1
        dsimp only [RawTape.span] at h
        change (q.work i).left.length + (q.work i).right.length ≤ t at ih
        omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact Nat.add_le_add_left (hsum.trans (Nat.mul_le_mul_left k (Nat.le_succ t))) _

/-- Once the source has halted, its raw output is the complete computed output. -/
private theorem output_run_of_halt (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) {t : ℕ} (ht : (Data.run tm input t).state = none) :
    (Data.run tm input t).output = output := by
  obtain ⟨u, hu, hout⟩ := hc
  have hou : (Data.run tm input u).output = output := (Data.output_run tm input u).trans hout
  rcases le_total t u with htu | hut
  · rwa [Data.run_eq_of_halt tm input htu ht] at hou
  · rw [Data.run_eq_of_halt tm input hut ((Data.state_run tm input u).trans hu), hou]

/-- A native computation is simulated with a linear clock, including clearing every auxiliary
stack, reversing its output and restoring Mathlib's canonical halting control. -/
def outputsInTime [Fintype State] (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {t : ℕ} (hc : tm.Computes input output)
    (ht : tm.RunsInTime input t) :
    TM2OutputsInTime (machine tm.q₀ tm.tr) input (some output)
      (input.length + (k + 1) * (t + 1) + output.length + 3) := by
  classical
  let hex := exists_haltsAt (runsInTime_iff_halted.mp ht)
  let u := hex.choose
  have hu := hex.choose_spec
  let d := Data.run tm input u
  have hd : d.state = none := (Data.state_run tm input u).trans hu.2.halted
  have ho : d.output = output := output_run_of_halt tm hc hd
  let cfg : (machine tm.q₀ tm.tr).Cfg :=
    ⟨some .clean, control d d.input.right.head? false, store d⟩
  have hstep : (machine tm.q₀ tm.tr).step (encode d) = some cfg := step_encode_halt tm d hd
  have hclean := cleanupEvals tm.q₀ tm.tr cfg rfl
  have htail := StateTransition.EvalsToInTime.cons hstep hclean
  change StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
    (some (haltList (machine tm.q₀ tm.tr) (d.output.reverse.reverse ++ [])))
    (auxiliaryLength (store d) + d.output.reverse.length + 2 + 1) at htail
  have htail' : StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
      (some (haltList (machine tm.q₀ tm.tr) output))
      (auxiliaryLength (store d) + d.output.length + 3) := by
    simpa only [cfg, store, List.reverse_reverse, List.append_nil, List.length_reverse,
      Nat.add_assoc, Nat.reduceAdd, ho] using htail
  have hresult := StateTransition.EvalsToInTime.trans (machine tm.q₀ tm.tr).step
    u (auxiliaryLength (store d) + d.output.length + 3) _ _ _
    (prefixEvals tm input hu.2 le_rfl) htail'
  refine hresult.mono ?_
  have ha := auxiliaryLength_run_time_le tm input u
  have hm : k * (u + 1) ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega)
  dsimp only [d] at *
  rw [ho]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Terminating native computation yields terminating canonical TM2 computation. -/
def outputs [Fintype State] (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) : TM2Outputs (machine tm.q₀ tm.tr) input (some output) :=
  (outputsInTime tm hc (runsInTime_iff_halted.mpr hc.choose_spec.1)).toTM2Outputs

end

end Turing.MultiTapeTM.ToTM2

namespace Turing.MultiTapeTM

open Polynomial

/-- A native polynomial-time binary multi-tape computation gives a Mathlib TM2
certificate with the same input and output encodings. -/
theorem _root_.solution {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (h : ComputableInPolyTime f encIn encOut) :
    Nonempty (TM2ComputableInPolyTime encIn encOut f) := by
  obtain ⟨t, s, ht, _, k, State, hfinite, tm, htm⟩ := h
  obtain ⟨c, d, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  let : Fintype State := Fintype.ofFinite State
  let p : Polynomial ℕ := X + C (k+2) * (C c * (X + 1)^d + 1) + C 3
  refine ⟨{ tm := ToTM2.machine tm.q₀ tm.tr
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := p
            outputsFun := ?_ }⟩
  intro a
  let n := (encIn a).length
  have hOut : (encOut (f a)).length ≤ t n := by
    have h := (htm a).length_output_le
    exact h
  have hrun := ToTM2.outputsInTime tm (htm a).1 (htm a).2.1
  have htime : n + (k+1) * (t n + 1) + (encOut (f a)).length + 3 ≤ p.eval n := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    have hlinear := Nat.mul_le_mul_left (k+2) (Nat.succ_le_succ (ht n))
    simp only [Nat.add_mul, Nat.succ_eq_add_one, Nat.one_mul] at hlinear ⊢
    omega
  change TM2OutputsInTime (ToTM2.machine tm.q₀ tm.tr) (List.map id (encIn a))
    (some (List.map id (encOut (f a)))) (p.eval n)
  rw [List.map_id, List.map_id]
  exact hrun.mono htime

end Turing.MultiTapeTM
