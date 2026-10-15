-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Compiler.effects_argsCode
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:09:39.810586+00:00
-- url     : https://prove2.me/submissions/9118a78a-7c77-4157-bbb4-16de4dac8fa9

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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

/-- Every word is the word of its signed value. -/
theorem wd_toInt (w : BitVec W) : _root_.ThreeSumApsp.WordRam.wd W w.toInt = w := BitVec.ofInt_toInt

section

private theorem private_541561795d_wd_add (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a + _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a + b) := (BitVec.ofInt_add a b).symm
end


section

private theorem private_8987e813d5_wd_mul (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a * _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a * b) := (BitVec.ofInt_mul a b).symm
end


section

private theorem private_8745cc2b10_wd_sub (a b : ℤ) : _root_.ThreeSumApsp.WordRam.wd W a - _root_.ThreeSumApsp.WordRam.wd W b = _root_.ThreeSumApsp.WordRam.wd W (a - b) := by
  rw [sub_eq_add_neg a b, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, _root_.ThreeSumApsp.WordRam.wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
end










/-! ## Configurations and single steps -/





/-! ## Runs -/

























/-! ## Pieces of code -/















/-! ## Straight-line code -/







@[simp] theorem effects_nil (m : ℤ → BitVec W) : _root_.ThreeSumApsp.WordRam.effects [] m = m := rfl

@[simp] theorem effects_cons (i : _root_.EndStatement.Instr) (l : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (i :: l) m = _root_.ThreeSumApsp.WordRam.effects l (_root_.ThreeSumApsp.WordRam.effect i m) := rfl

theorem effects_append (l₁ l₂ : List _root_.EndStatement.Instr) (m : ℤ → BitVec W) :
    _root_.ThreeSumApsp.WordRam.effects (l₁ ++ l₂) m = _root_.ThreeSumApsp.WordRam.effects l₂ (_root_.ThreeSumApsp.WordRam.effects l₁ m) := by
  simp [_root_.ThreeSumApsp.WordRam.effects, List.foldl_append]







/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}



/-- The sum of two known numbers. -/
theorem effect_add (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.add i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a + b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_541561795d_wd_add]

/-- The difference of two known numbers. -/
theorem effect_sub (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.sub i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a - b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8745cc2b10_wd_sub]

/-- The product of two known numbers. -/
theorem effect_mul (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.mul i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (a * b)) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_8987e813d5_wd_mul]

/-- Loading from the address a that the cell j holds. -/
theorem effect_load (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a) (ha : _root_.ThreeSumApsp.WordRam.InRange W a) :
    _root_.ThreeSumApsp.WordRam.effect (_root_.EndStatement.Instr.load i j) m = Function.update m i (m a) := by
  rw [_root_.ThreeSumApsp.WordRam.effect, hj, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd ha]











end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}



theorem AgreeOutside.refl (s : Set ℤ) (m : ℤ → BitVec W) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m := Set.eqOn_refl m sᶜ

theorem AgreeOutside.trans (h₁ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₂) (h₂ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₂ m₃) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁

theorem AgreeOutside.mono (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m') (hst : s ⊆ t) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h



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



















end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/













section width

variable {F x p : ℕ} {o : _root_.Light.Op} {a b e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}



theorem Expr.vars_op_le_iff : (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := max_le_iff

theorem Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := max_le_iff

















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

/-- What an expression may change is scratch. -/
theorem temps_subset_scratch {k : ℕ} : _root_.Light.Compiler.Temps k F ⊆ _root_.Light.Compiler.Scratch F := by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))









/-! ## Addresses, and numbers that fit in a word -/

/-- The cell of the local variable x of the frame q, computed from FP and the pool. -/
theorem cStack_sub (q x : ℕ) : _root_.Light.Compiler.cStack q - ((2 * x : ℕ) : ℤ) = _root_.Light.Compiler.cStack (q + x) := by
  simp only [_root_.Light.Compiler.cStack]
  push_cast
  ring





/-- The addresses of the stack fit in a word. -/
theorem Sizes.inRange_stack (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : _root_.ThreeSumApsp.WordRam.InRange W (_root_.Light.Compiler.cStack j) := by
  have hjQ : (j : ℤ) ≤ Z.Q := by exact_mod_cast hj
  constructor <;> simp only [_root_.Light.Compiler.cStack] <;> linarith [Z.fits.stack]

/-- The addresses of the memory fit in a word. -/
theorem Sizes.inRange_addr (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) {a : ℤ} (h : Z.lim.Addr a) : _root_.ThreeSumApsp.WordRam.InRange W a := by
  constructor <;> linarith [Z.fits.space, h.1, h.2]



/-! ## The relation between a state of the light language and a memory of the machine -/



section Rel

variable {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {q q' : ℕ} {m m' : ℤ → BitVec W}

/-- After a change that spares the numbers 1, 0, -1 and the pool, the new memory represents a state
as soon as FP, the local variables and the memory cells are right. -/
theorem Rel.of_agreeOutside {s : Set ℤ} (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside s m m')
    (hs : s ⊆ (_root_.Light.Compiler.Constants Z.disp)ᶜ) (hfp : m' _root_.Light.Compiler.cFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q'))
    (hloc : ∀ x < Z.F, m' (_root_.Light.Compiler.cStack (q' + x)) = _root_.ThreeSumApsp.WordRam.wd W (σ'.loc x))
    (hmem : ∀ a < Z.lim.space, m' (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (σ'.mem a)) : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ' q' m' := by
  have keep {a : ℤ} (ha : a ∈ _root_.Light.Compiler.Constants Z.disp) : m' a = m a := A.cell fun h => hs h ha
  exact {
    one := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.one
    zero := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.zero
    neg := (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans R.neg
    pool := fun n hn => (keep (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))).trans (R.pool n hn)
    fp := hfp
    loc := hloc
    mem := hmem }

/-- A memory that differs only in scratch cells represents the same state. -/
theorem Rel.same (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m' :=
  R.of_agreeOutside A (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) R.fp)
    (fun x hx => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.loc x hx)) fun a ha => A.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (R.mem a ha)







/-- Reading a memory cell. -/
theorem Rel.read (R : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = _root_.ThreeSumApsp.WordRam.wd W (σ.mem a.toNat) := by
  have := R.mem a.toNat (by have := ha.1; have := ha.2; omega)
  rwa [Int.toNat_of_nonneg ha.1] at this



end Rel



/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}

/-- A memory that differs only in scratch cells represents the same state in the same frame. -/
theorem Framed.same (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (A : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch Z.F) m m') : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m' :=
  ⟨I.rel.same A, I.low, I.high⟩





end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler is correct on expressions

The code of an expression e, compiled for the temporary T_k, only changes the memory
(`straight_compileExpr`).  Run in a memory that represents the state σ, it leaves the value of e in
T_k and changes nothing but ADDR and the temporaries from T_k on.  That is `effects_compileExpr`,
for an expression that needs no more temporaries than there are from T_k on, and
`effects_compileExpr_of_width`, the form that the other files use, for an expression of width at
most F.

The proof is an induction on e; in each case the instructions are run one after the other.  A
constant is built from its binary digits (`effects_digitsCode`).  For an operation, the value of the
left side waits in T_k while the right side is evaluated into T_{k+1}, which does not touch T_k.
-/

public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


variable {W : ℕ} {F : ℕ}

section


/-- Every expression uses at least one temporary. -/
private theorem _root_.ThreeSum1960614.Machine.Light.Expr.private_12b548b970_height_pos (e : _root_.ThreeSum1960614.Machine.Light.Expr) : 0 < e.height := by
  induction e with
  | const n => simp [_root_.ThreeSum1960614.Machine.Light.Expr.height]
  | var x => simp [_root_.ThreeSum1960614.Machine.Light.Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih
end


section

/-- The temporary that receives the value of an expression is one of those that its code may
change. -/
private theorem private_ea85bee431_cT_mem_temps_of_height (e : _root_.ThreeSum1960614.Machine.Light.Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) :
    _root_.Light.Compiler.cT k ∈ _root_.Light.Compiler.Temps k F := by
  have := e.private_12b548b970_height_pos
  ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
end


/-! ## Constants -/



section

/-- The code for a constant: the cell c receives the number with the given binary digits, and
nothing else changes. -/
private theorem private_9b09e22f2f_effects_digitsCode {c : ℤ} (hc : _root_.Light.Compiler.cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2)
    (m : ℤ → BitVec W) (hone : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.digitsCode c L) m c = _root_.ThreeSumApsp.WordRam.wd W (Nat.ofDigits 2 L : ℕ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside {c} m (_root_.ThreeSumApsp.WordRam.effects (_root_.Light.Compiler.digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    rw [_root_.Light.Compiler.digitsCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub c (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.wd_toInt (m c)).symm (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L ih =>
    obtain ⟨val, A⟩ := ih fun x hx => hL x (by simp [hx])
    -- c := c + c
    rw [_root_.Light.Compiler.digitsCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      rw [if_neg one_ne_zero, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add c (Function.update_self _ _ _)
        ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
end


/-! ## Expressions -/





section

/-- The instruction of an operation, on cells that hold known numbers. -/
private theorem private_110484d29f_effect_instr (o : _root_.Light.Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = _root_.ThreeSumApsp.WordRam.wd W a)
    (hk : m k = _root_.ThreeSumApsp.WordRam.wd W b) : _root_.ThreeSumApsp.WordRam.effect (o.instr i j k) m = Function.update m i (_root_.ThreeSumApsp.WordRam.wd W (o.eval a b)) := by
  cases o
  exacts [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_add i hj hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub i hj hk, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_mul i hj hk]
end


variable {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}

section

/-- The code of an expression leaves its value in T_k and changes nothing but ADDR and the
temporaries from T_k on. -/
private theorem private_4eead6d256_effects_compileExpr (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) (hvars : e.vars ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hT : k + e.height ≤ 2 * Z.F + 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m (_root_.Light.Compiler.cT k) = _root_.ThreeSumApsp.WordRam.wd W (e.val σ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m) := by
  induction e generalizing k m with
  | const n =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.private_9b09e22f2f_effects_digitsCode (c := _root_.Light.Compiler.cT k) (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) (Nat.digits 2 n)
      (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    -- ADDR := FP - 2 x; T_k := the cell at ADDR
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_sub _root_.Light.Compiler.cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)), _root_.ThreeSum1960614.Machine.Light.Compiler.cStack_sub,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_load (_root_.Light.Compiler.cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine ⟨?_, ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m).update (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) _).update hk _⟩
    rw [Function.update_self, Function.update_of_ne (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), I.rel.loc x hx, _root_.ThreeSum1960614.Machine.Light.Expr.val]
  | op o a b iha ihb =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (_root_.ThreeSum1960614.Machine.Light.Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := _root_.ThreeSum1960614.Machine.Light.Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ := ihb (I.same (Aa.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch)) (k + 1) hwb hsb (by omega)
    -- T_k := T_k o T_{k+1}
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.Light.Compiler.private_110484d29f_effect_instr o (_root_.Light.Compiler.cT k) (Ab.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) va) vb]
    exact ⟨Function.update_self _ _ _,
      (Aa.trans (Ab.mono (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))))).update hk _⟩
  | load a ih =>
    have hk := _root_.ThreeSum1960614.Machine.Light.Compiler.private_ea85bee431_cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    -- the address is not negative, so it is neither ADDR nor a temporary
    have hnonneg : 0 ≤ a.val σ := haddr.1
    -- T_k := the cell at T_k
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_cons, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_nil,
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effect_load (_root_.Light.Compiler.cT k) va (Z.inRange_addr haddr), Aa.cell (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))), I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩
end


/-- The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
its value in T_k and changes nothing but ADDR and the temporaries from T_k on. -/
theorem effects_compileExpr_of_width (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m (_root_.Light.Compiler.cT k) = _root_.ThreeSumApsp.WordRam.wd W (e.val σ) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k) m) :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.private_4eead6d256_effects_compileExpr I e k (_root_.ThreeSum1960614.Machine.Light.Expr.width_le_iff.1 hw).1 hs
    (by have := (_root_.ThreeSum1960614.Machine.Light.Expr.width_le_iff.1 hw).2; omega)

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

variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q : ℕ} {m : ℤ → BitVec W}
section

/-- The code of the arguments leaves their values in T_k, T_{k+1}, … and changes nothing but ADDR
and the temporaries from T_k on. -/
theorem ThreeSum1960614.Machine.Light.Compiler.effects_argsCode__implementation_7491417883 (I : _root_.ThreeSum1960614.Machine.Light.Compiler.Framed Z σ q m) (es : List _root_.ThreeSum1960614.Machine.Light.Expr) (k : ℕ)
    (hw : ∀ e ∈ es, e.width ≤ Z.F) (hs : ∀ e ∈ es, e.Safe Z.lim σ)
    (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length,
        _root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k) m (_root_.Light.Compiler.cT (k + i)) = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.frame (es.map (·.val σ)) i)) ∧
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Temps k Z.F) m (_root_.ThreeSumApsp.WordRam.effects (_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode es k) m) := by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := _root_.ThreeSum1960614.Machine.Light.Compiler.effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono _root_.ThreeSum1960614.Machine.Light.Compiler.temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [_root_.ThreeSum1960614.Machine.Light.Compiler.argsCode, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.effects_append]
    refine ⟨fun i hi => ?_, Ae.trans (Aes.mono (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))))⟩
    cases i with
    | zero => exact Aes.read (by ((simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch, _root_.ThreeSum1960614.Machine.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_temps_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_stack_iff, _root_.ThreeSum1960614.Machine.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))) ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Compiler.effects_argsCode__implementation_7491417883) := (@ThreeSum1960614.Machine.Light.Compiler.effects_argsCode__implementation_7491417883)

#print axioms solution
