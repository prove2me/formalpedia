-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.steps_start
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:21:08.274801+00:00
-- url     : https://prove2.me/submissions/df11045b-ca96-441a-9073-a1f41e4b35a9

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

variable {W : ℕ} {P : List _root_.EndStatement.Instr}

/-! ## Words -/





/-- The word of a number in the range of words, read as a signed number, is that number. -/
theorem toInt_wd {v : ℤ} (h : _root_.ThreeSumApsp.WordRam.InRange W v) : (_root_.ThreeSumApsp.WordRam.wd W v).toInt = v := by
  obtain ⟨hlo, hhi⟩ := h
  rw [BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> push_cast <;> linarith







section

private theorem private_8745cc2b10_wd_sub (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a - _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a - b) := by
  rw [sub_eq_add_neg a b, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
end


section

private theorem private_6b248825b2_wd_one : (1 : BitVec W) = _root_.ThreeSumApsp.WordRam.wd W 1 := BitVec.eq_of_toNat_eq rfl
end








/-! ## Configurations and single steps -/





/-! ## Runs -/





section


private theorem Steps.private_ba3d5eb361_one {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSumApsp.WordRam.step P c = .inl c') : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 c c' := ⟨c', h, rfl⟩
end


/-- One run after the other. -/
theorem Steps.trans {n k : ℕ} {c c₁ c₂ : _root_.ThreeSumApsp.WordRam.Cfg W} (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c₁) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P k c₁ c₂) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P (n + k) c c₂ := by
  induction n generalizing c with
  | zero => obtain rfl := h₁; simpa using h₂
  | succ n ih =>
    obtain ⟨c', hs, hr⟩ := h₁
    rw [Nat.add_right_comm]
    exact ⟨c', hs, ih hr⟩

/-- A run, with its last position written differently. -/
theorem Steps.cast_pos {n p p' : ℕ} {c : _root_.ThreeSumApsp.WordRam.Cfg W} {m : ℤ → BitVec W} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨p, m⟩)
    (hp : p = p') : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c ⟨p', m⟩ := hp ▸ h

/-- A run, with its number of steps written differently. -/
theorem Steps.cast_count {n n' : ℕ} {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n c c') (hn : n = n') :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P n' c c' := hn ▸ h













/-! ## Pieces of code -/



/-- The whole program, from position 0 on. -/
theorem codeAt_self (l : List _root_.EndStatement.Instr) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt l 0 l := List.prefix_refl l

/-- The first part of a piece of code. -/
theorem CodeAt.left {pos : ℕ} {l₁ l₂ : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (l₁ ++ l₂)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h

/-- The second part of a piece of code follows the first. -/
theorem CodeAt.right {pos : ℕ} {l₁ l₂ : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (l₁ ++ l₂)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]

/-- The first instruction of a piece of code is the one that the machine finds at its position. -/
theorem CodeAt.head {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    P.getD pos _root_.EndStatement.Instr.reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- A piece of code without its first instruction. -/
theorem CodeAt.tail {pos : ℕ} {i : _root_.EndStatement.Instr} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (i :: l)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P (pos + 1) l :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt.right (l₁ := [i]) h

/-- A piece of code, with its position written differently. -/
theorem CodeAt.cast_pos {pos pos' : ℕ} {l : List _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos l) (hp : pos = pos') :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos' l := hp ▸ h

/-! ## Straight-line code -/







@[simp] theorem effects_nil (m : ℤ → BitVec W) : _root_.ThreeSumApsp.WordRam.effects [] m = m := rfl

@[simp] theorem effects_cons (i : _root_.EndStatement.Instr) (l : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (i :: l) m = _root_.ThreeSumApsp.WordRam.effects l (_root_.ThreeSumApsp.WordRam.effect i m) := rfl

theorem effects_append (l₁ l₂ : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (l₁ ++ l₂) m = _root_.ThreeSumApsp.WordRam.effects l₂ (_root_.ThreeSumApsp.WordRam.effects l₁ m) := by
  simp [_root_.ThreeSumApsp.WordRam.effects, List.foldl_append]

section

private theorem private_1baa6e787a_step_straight {c : _root_.ThreeSumApsp.WordRam.Cfg W} {i : _root_.EndStatement.Instr} (h : P.getD c.pc _root_.EndStatement.Instr.reject = i)
    (hi : _root_.ThreeSumApsp.WordRam.Straight i) : _root_.ThreeSumApsp.WordRam.step P c = .inl ⟨c.pc + 1, _root_.ThreeSumApsp.WordRam.effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [_root_.ThreeSumApsp.WordRam.Straight] at hi <;> simp only [_root_.ThreeSumApsp.WordRam.step, h, _root_.ThreeSumApsp.WordRam.effect, write, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_6b248825b2_wd_one]
end




/-- A list of instructions that only change the memory. -/
theorem steps_straight (l : List _root_.EndStatement.Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pc l)
    (hl : ∀ i ∈ l, _root_.ThreeSumApsp.WordRam.Straight i) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, _root_.ThreeSumApsp.WordRam.effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_1baa6e787a_step_straight hcode.head hi,
      (ih (pc + 1) (_root_.ThreeSumApsp.WordRam.effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩

/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

/-- The only constant. -/
theorem effect_one (i : ℤ) : _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.one i) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W 1) := rfl



/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]















end known

/-! ## Branches and verdicts -/

/-- A branch on a cell that holds the number v: to l if v is negative, else to the next position. -/
theorem steps_bltz {rest : List _root_.EndStatement.Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt P pos (_root_.EndStatement.Instr.bltz c l :: rest)) (hc : m c = _root_.ThreeSumApsp.WordRam.wd W v) (hv : _root_.ThreeSumApsp.WordRam.InRange W v) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps.private_ba3d5eb361_one ?_
  simp only [_root_.ThreeSumApsp.WordRam.step, hcode.head, hc, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd hv]







/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}



theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁





/-- A cell outside s is unchanged. -/
theorem AgreeOutside.cell (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha

/-- A cell outside s still holds v. -/
theorem AgreeOutside.read (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∉ s) {v : BitVec W} (hv : m a = v) :
    m' a = v :=
  (h ha).trans hv

/-- Writing a cell of s. -/
theorem AgreeOutside.update (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (ha : a ∈ s) (v : BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (Function.update m' a v) :=
  fun x hx => (Function.update_of_ne (fun e : x = a => hx (e ▸ ha)) _ _).trans (h hx)



theorem WritesIn.mono {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn t i := by
  cases i <;> first | exact hst h | exact h

section

private theorem private_e74ef30073_agreeOutside_effect {i : _root_.EndStatement.Instr} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effect i m) := by
  cases i <;>
    first | exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m).update h _ | exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m | exact h.elim
end


/-- Code without stores changes only the cells that its instructions name as their targets. -/
theorem agreeOutside_effects {l : List _root_.EndStatement.Instr} (h : ∀ i ∈ l, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn s i) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m (_root_.ThreeSumApsp.WordRam.effects l m) := by
  induction l generalizing m with
  | nil => exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_e74ef30073_agreeOutside_effect hi m).trans (ih hl _)

end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/

@[expose] public section

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/


















/-! ## Expressions and tests -/















/-! ## Statements -/

























/-! ## Lengths -/

section

private theorem private_2e2c0c0be3_length_digitsCode (c : ℤ) (L : List ℕ) : (_root_.Light.Compiler.digitsCode c L).length = _root_.Light.Compiler.digitsLen L := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [_root_.Light.Compiler.digitsCode, _root_.Light.Compiler.digitsLen, List.length_append, ih, List.length_singleton]
    split_ifs <;> rfl
end


/-- The code of an expression has the length defined on the text. -/
theorem length_compileExpr (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k).length = e.size := by
  induction e generalizing k with
  | const n => exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_2e2c0c0be3_length_digitsCode _ _
  | var x => rfl
  | op o a b iha ihb => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.Light.Expr.size, iha, ihb]
  | load a ih => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.Light.Expr.size, ih]

/-- The code of a test has the length defined on the text. -/
theorem length_compileCond (c : _root_.ThreeSum1960614.Machine.Light.Cond) (l : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c l).length = c.size := by
  cases c <;> simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileCond, _root_.ThreeSum1960614.Machine.Light.Cond.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]

/-- The code for the arguments of a call has the length defined on the text. -/
theorem length_argsCode (es : List _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) : (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k).length = _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize es := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode, _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr, ih]





section

/-- A call up to its jump has the length defined on the text. -/
private theorem private_d68abacb3f_length_callCode (G : _root_.Light.Compiler.CodeLayout) (p : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) (ret : ℕ) :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.callCode G p args ret).length = _root_.ThreeSum1960614.Machine.Light.Compiler.callSize G.F args := by
  simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.callCode, _root_.ThreeSum1960614.Machine.Light.Compiler.callSize, _root_.ThreeSum1960614.Machine.Light.Compiler.length_argsCode, _root_.Light.Compiler.length_newFrame]
end




/-- The code of a statement has the length defined on the text. -/
theorem length_compileStmt (G : _root_.Light.Compiler.CodeLayout) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ) :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G s pos).length = s.size G.F := by
  induction s generalizing pos with
  | skip => rfl
  | set x e => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]
  | store a e => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileExpr]
  | seq s t ihs iht => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ihs, iht]
  | ite c s t ihs iht => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ihs, iht, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond]
  | «while» c s ih => simp +arith [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, ih, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileCond]
  | call p args x => simp [_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.private_d68abacb3f_length_callCode]

end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/













section width

variable {F x p : ℕ} {o : _root_.Light.Op} {a b e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}























end width

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The numbers that never change -/







/-! ## Sets of cells -/















/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/













variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}











/-! ## Addresses, and numbers that fit in a word -/













/-! ## The relation between a state of the light language and a memory of the machine -/



section Rel

variable {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {q q' : ℕ} {m m' : ℤ → BitVec W}















end Rel



/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}



/-- An unconditional jump. -/
theorem steps_jump {l : ℕ} (hcode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code pos (_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG l :: rest))
    (hneg : m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1)) (hr : _root_.ThreeSumApsp.WordRam.InRange W (-1)) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code 1 ⟨pos, m⟩ ⟨l, m⟩ := by
  simpa using _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_bltz hcode hneg hr



end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The dispatcher

The machine has no indirect jump.  A return loads the position r to return to into the register RR
and jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, ….  It
arrives at position r after 2 (r + 1) steps and changes no cell but RR (`steps_dispatcher`).

The proof runs one pair of instructions (`steps_dispatcher_pair`) and then counts down: from the
j-th pair on, with k in RR, the machine arrives at position j + k (`steps_dispatcher_from`).
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

variable {W : ℕ} {code : List _root_.EndStatement.Instr} {disp n : ℕ}



/-- Two instructions for each position. -/
theorem length_dispatcher (n : ℕ) : (_root_.Light.Compiler.dispatcher n).length = 2 * n := by
  simp [_root_.Light.Compiler.dispatcher, List.length_flatMap, Nat.mul_comm]











end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The number read off the text -/



/-- The outermost frame has room for the result and the two arguments. -/
theorem three_le_frameSize (P : _root_.ThreeSum1960614.Machine.Light.Program) : 3 ≤ _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P := le_max_left _ _



/-! ## The parts of the code -/







































/-! ## Lengths and positions -/



/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (_root_.ThreeSum1960614.Machine.Light.mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [_root_.ThreeSum1960614.Machine.Light.mainStmt, _root_.ThreeSum1960614.Machine.Light.Stmt.size, _root_.ThreeSum1960614.Machine.Light.Compiler.callSize, _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize, _root_.ThreeSum1960614.Machine.Light.Expr.size]



section

private theorem private_5cb4f1262a_length_tailCode (dec : Bool) (pos : ℕ) :
    (_root_.Light.Compiler.tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl
end




section

private theorem private_2d601c1e00_length_bodiesCode (G : _root_.Light.Compiler.CodeLayout) :
    ∀ (bs : List _root_.ThreeSum1960614.Machine.Light.Stmt) (pos : ℕ), pos + (_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode G bs pos).length = _root_.ThreeSum1960614.Machine.Light.Compiler.endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := private_2d601c1e00_length_bodiesCode G bs (pos + b.size G.F + _root_.Light.Compiler.epilogueSize)
    simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode, _root_.ThreeSum1960614.Machine.Light.Compiler.endPos, List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt, _root_.Light.Compiler.length_epilogue]
    omega
end


section parts

variable (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool)

section

private theorem private_84d869635b_length_through_mainCode :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec).length = _root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec := by
  simp only [_root_.ThreeSum1960614.Machine.Light.Compiler.headCode, _root_.Light.Compiler.headStraight, _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode, List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.length_compileStmt,
    _root_.ThreeSum1960614.Machine.Light.Compiler.size_mainStmt, _root_.ThreeSum1960614.Machine.Light.Compiler.private_5cb4f1262a_length_tailCode, _root_.ThreeSum1960614.Machine.Light.Compiler.firstBody, _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos, _root_.Light.Compiler.mainPos, _root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout, List.length_cons,
    List.length_nil]
  omega
end


section

private theorem private_702e8e60fa_length_through_bodiesCode :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec ++
      _root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec)).length = _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec := by
  rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.private_84d869635b_length_through_mainCode]
  exact _root_.ThreeSum1960614.Machine.Light.Compiler.private_2d601c1e00_length_bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P _
end


section

private theorem private_625a543f55_length_through_dispatcher :
    (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec ++
      _root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec) ++
      _root_.Light.Compiler.dispatcher (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec)).length = 3 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec := by
  rw [List.length_append, _root_.ThreeSum1960614.Machine.Light.Compiler.private_702e8e60fa_length_through_bodiesCode, _root_.ThreeSum1960614.Machine.Light.Compiler.length_dispatcher]
  omega
end


/-- The first part is at position 0. -/
theorem codeAt_headCode : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) 0 (_root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec) :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.codeAt_self _).left.left.left.left











/-- The start-up code follows the dispatcher. -/
theorem codeAt_startCode :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (3 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.startCode P dec) :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.codeAt_self _).right.cast_pos (by rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_625a543f55_length_through_dispatcher, Nat.zero_add])

end parts



end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

section

private theorem private_39e5ba589c_effects_headStraight (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m =
      Function.update (Function.update (Function.update m _root_.Light.Compiler.cONE (_root_.ThreeSumApsp.WordRam.wd W 1)) _root_.Light.Compiler.cZERO (_root_.ThreeSumApsp.WordRam.wd W 0)) _root_.Light.Compiler.cNEG
        (_root_.ThreeSumApsp.WordRam.wd W (-1)) := by
  simp only [_root_.Light.Compiler.headStraight, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil]
  rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_one, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cZERO (by (repeat
                                                                                                                                                                        (first
                                                                                                                                                                          | rw [_root_.Function.update_self]
                                                                                                                                                                          | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                                                                                       (first
                                                                                                                                                                                         | rw [_root_.Function.update_self]
                                                                                                                                                                                         | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))),
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cNEG (by (repeat
                                                                                                     (first
                                                                                                       | rw [_root_.Function.update_self]
                                                                                                       | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))) (by (repeat
                                                                                                                    (first
                                                                                                                      | rw [_root_.Function.update_self]
                                                                                                                      | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))])))]
  rfl
end


section

/-- The three registers after the first three instructions. -/
private theorem private_022aab1f82_effects_headStraight_consts (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1 ∧ _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0 ∧
      _root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1) := by
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_39e5ba589c_effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> (repeat
                             (first
                               | rw [_root_.Function.update_self]
                               | rw [_root_.Function.update_of_ne (by (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
end


/-! ## The pool -/



section

private theorem private_1689400533_agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Pool N) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.poolCode N)
    (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show _root_.Light.Compiler.cPool 0 ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · have := List.mem_range.1 hn
    show _root_.Light.Compiler.cPool (n + 1) ∈ _root_.Light.Compiler.Pool N
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




section

/-- The memory after the first three instructions and the code for the pool. -/
private def private_54239f6749_poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.poolCode N) (_root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m)
end




section

/-- The code for the pool leaves the numbers 1, 0, -1 in their registers. -/
private theorem private_e83a5c8f0a_poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1 ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0 ∧ _root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1) := by
  obtain ⟨one, zero, neg⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_022aab1f82_effects_headStraight_consts m
  have keep := _root_.ThreeSum1960614.Machine.Light.Compiler.private_1689400533_agreeOutside_poolCode N (_root_.ThreeSumApsp.WordRam.effects _root_.Light.Compiler.headStraight m)
  exact ⟨keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) one, keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) zero, keep.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) neg⟩
end




/-! ## The outermost frame -/



section

/-- The instructions of `zeroCode` write into the outermost frame. -/
private theorem private_71d3c3537a_writesIn_zeroCode (F : ℕ) : ∀ i ∈ _root_.Light.Compiler.zeroCode F, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.WritesIn (_root_.Light.Compiler.MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + x) ∈ _root_.Light.Compiler.MainFrame F
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




section

private theorem private_9d050fcb47_agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside ({_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.MainFrame F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) m) := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.agreeOutside_effects (l := _root_.Light.Compiler.frameCode F) (List.forall_mem_cons.2 ⟨?_,
    List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_,
      List.forall_mem_singleton.2 ?_⟩⟩⟩) m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (_root_.ThreeSum1960614.Machine.Light.Compiler.private_71d3c3537a_writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 1) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
  · -- local variable 2 := the second argument
    show _root_.Light.Compiler.cStack (_root_.Light.Compiler.mainFrame + 2) ∈ _
    ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end




/-! ## The memory in which the outermost statement starts -/



section

private theorem private_1410a86b87_startMem_eq (F N : ℕ) (m : ℤ → BitVec W) :
    _root_.Light.Compiler.startMem F N m = _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.frameCode F) (_root_.ThreeSum1960614.Machine.Light.Compiler.private_54239f6749_poolMem N m) := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append _ _ _
end






/-! ## The run from the first instruction to the outermost statement -/

section

private theorem private_cd85c527ea_straight_headStraight : ∀ i ∈ _root_.Light.Compiler.headStraight, _root_.ThreeSumApsp.WordRam.Straight i := by
  simp [_root_.Light.Compiler.headStraight, _root_.ThreeSumApsp.WordRam.Straight]
end


section

private theorem private_ade1d6c544_straight_startStraight (F N : ℕ) : ∀ i ∈ _root_.Light.Compiler.startStraight F N, _root_.ThreeSumApsp.WordRam.Straight i := by
  simp [_root_.Light.Compiler.startStraight, _root_.Light.Compiler.poolCode, _root_.Light.Compiler.frameCode, _root_.Light.Compiler.zeroCode, _root_.ThreeSumApsp.WordRam.Straight, or_imp, forall_and]
end


section

private theorem private_53b1af45d1_length_startStraight (F N : ℕ) : (_root_.Light.Compiler.startStraight F N).length = N + F + 4 := by
  simp +arith [_root_.Light.Compiler.startStraight, _root_.Light.Compiler.poolCode, _root_.Light.Compiler.frameCode, _root_.Light.Compiler.zeroCode]
end




end Light.Compiler

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
section

/-- From the first instruction to the outermost statement. -/
theorem ThreeSum1960614.Machine.Light.Compiler.steps_start__implementation_441fc0a44b (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) (hneg : _root_.ThreeSumApsp.WordRam.InRange W (-1))
    (m : ℤ → BitVec W) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec + _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 9) ⟨0, m⟩
      ⟨_root_.Light.Compiler.mainPos, _root_.Light.Compiler.startMem (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) m⟩ := by
  have head := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_headCode P p0 dec
  have start := _root_.ThreeSum1960614.Machine.Light.Compiler.codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_022aab1f82_effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_e83a5c8f0a_poolMem_consts (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) m
  have neg₁ : _root_.Light.Compiler.startMem (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1) := by
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_1410a86b87_startMem_eq, (_root_.ThreeSum1960614.Machine.Light.Compiler.private_9d050fcb47_agreeOutside_frameCode (_root_.ThreeSum1960614.Machine.Light.Compiler.three_le_frameSize P) _).cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), neg]
  -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
  refine ((((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_straight _ 0 m head.left _root_.ThreeSum1960614.Machine.Light.Compiler.private_cd85c527ea_straight_headStraight).trans
    (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump head.right neg₀ hneg)).trans
    (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.steps_straight _ _ _ start.left (_root_.ThreeSum1960614.Machine.Light.Compiler.private_ade1d6c544_straight_startStraight _ _))).trans
    (_root_.ThreeSum1960614.Machine.Light.Compiler.steps_jump start.right neg₁ hneg)).cast_count ?_
  rw [_root_.ThreeSum1960614.Machine.Light.Compiler.private_53b1af45d1_length_startStraight, show _root_.Light.Compiler.headStraight.length = 3 from rfl]
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.steps_start__implementation_441fc0a44b) := (@ThreeSum1960614.Machine.Light.Compiler.steps_start__implementation_441fc0a44b)

#print axioms solution
