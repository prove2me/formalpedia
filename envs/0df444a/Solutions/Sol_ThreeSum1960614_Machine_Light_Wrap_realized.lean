-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Wrap.realized
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:16:34.145505+00:00
-- url     : https://prove2.me/submissions/ed48215f-e5ff-4d87-9930-00d763384410

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Compiler_compileProgram_correct
import Theorems.Thm_ThreeSum1960614_Machine_Light_Wrap_topSolves
import Theorems.Thm_ThreeSum1960614_Machine_Light_fits_of_small

local instance platformRadixNonzero_fd7e328953 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace Light.Wrap
end Light.Wrap
namespace List
end List
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.Light.Wrap
end ThreeSum1960614.Machine.Light.Wrap
namespace ThreeSum1960614.Machine.List
end ThreeSum1960614.Machine.List
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
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/













/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : _root_.ThreeSumApsp.WordRam.Problem} {P : List _root_.EndStatement.Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



/-! ## Bounds up to a constant -/





/-! ## Bounds in one size -/









end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

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











/-- Numbers of absolute value at most B are in the range of words if 2 B < 2^W. -/
theorem inRange_of_abs_le {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : _root_.ThreeSumApsp.WordRam.InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- The initial memory holds the input in the cells 0, 1, 2, …, followed by zeros. -/
theorem loadWords_mem_nat (W : ℕ) (ws : List ℤ) (a : ℕ) :
    _root_.EndStatement.loadWords W ws (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (ws.getD a 0) := by
  simp [_root_.EndStatement.loadWords, show ¬ ((a : ℤ) < 0) by omega]

/-- The negative cells of the initial memory hold zeros. -/
theorem loadWords_mem_neg (W : ℕ) (ws : List ℤ) {a : ℤ} (ha : a < 0) :
    _root_.EndStatement.loadWords W ws a = _root_.ThreeSumApsp.WordRam.wd W 0 := by
  simp [_root_.EndStatement.loadWords, ha]

/-! ## Configurations and single steps -/





/-! ## Runs -/

























/-! ## Pieces of code -/















/-! ## Straight-line code -/



















/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}





















end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

























end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List
open _root_.List


variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]

















/-! ## Blocks one after the other -/

















/-! ## Sums -/













section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]





end









/-! ## A running minimum -/





/-! ## Counting -/

















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp
open _root_.ThreeSumApsp


variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/







/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  _root_.ThreeSum1960614.Machine.List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/





end ThreeSumApsp

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



/-- A number within the limit on words is in the range of words. -/
theorem Fits.inRange {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {N Q : ℕ} (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim N Q) {v : ℤ}
    (h : |v| ≤ lim.word) : _root_.ThreeSumApsp.WordRam.InRange W v :=
  _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.inRange_of_abs_le (by have := hfit.word; have := (abs_nonneg v).trans h; omega) h



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







end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

/-! ## The notion for light programs -/









/-! ## The word size -/











/-! ## Time and space -/





/-- The time of a compiled program. -/
theorem ramSteps_le (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) (c : ℕ) :
    (_root_.ThreeSum1960614.Machine.Light.ramSteps P dec c : ℝ) ≤ (_root_.ThreeSum1960614.Machine.Light.timeConst P dec : ℝ) * (c : ℝ) + _root_.ThreeSum1960614.Machine.Light.timeConst P dec := by
  have hstart : _root_.ThreeSum1960614.Machine.Light.Compiler.startCost P dec ≤ _root_.ThreeSum1960614.Machine.Light.timeConst P dec := by unfold _root_.ThreeSum1960614.Machine.Light.timeConst; omega
  have hsim : _root_.Light.Compiler.stepsPerStep (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) ≤ _root_.ThreeSum1960614.Machine.Light.timeConst P dec := by unfold _root_.ThreeSum1960614.Machine.Light.timeConst; omega
  have : _root_.ThreeSum1960614.Machine.Light.ramSteps P dec c ≤ _root_.ThreeSum1960614.Machine.Light.timeConst P dec * c + _root_.ThreeSum1960614.Machine.Light.timeConst P dec :=
    (Nat.add_comm _ _).trans_le (Nat.add_le_add (Nat.mul_le_mul_right c hsim) hstart)
  exact_mod_cast this

section

private theorem private_f79d03ee75_ramSteps_le_of_le (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) {c : ℕ} {T : ℝ} (h : (c : ℝ) ≤ T) :
    (_root_.ThreeSum1960614.Machine.Light.ramSteps P dec c : ℝ) ≤ (_root_.ThreeSum1960614.Machine.Light.timeConst P dec : ℝ) * T + _root_.ThreeSum1960614.Machine.Light.timeConst P dec :=
  (_root_.ThreeSum1960614.Machine.Light.ramSteps_le P dec c).trans (by gcongr)
end






/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}

/-- The initial memory holds the input, and zeros in the cells of the two arguments. -/
theorem input_loadWords (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Compiler.Input lim (_root_.Light.memOf ws) 0 0 (_root_.EndStatement.loadWords W ws) where
  rep := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.loadWords_mem_nat W ws
  bounded := _root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe.abs_getD_le h0 h
  arg1 := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.loadWords_mem_neg W ws (by decide)
  arg2 := _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.loadWords_mem_neg W ws (by decide)
  arg1_le := by simpa using h0
  arg2_le := by simpa using h0

/-- Reading the output: a cell of a memory that holds μ, as a signed word. -/
theorem Compiler.Holds.output {c : ℤ → BitVec W} (h : _root_.ThreeSum1960614.Machine.Light.Compiler.Holds W lim μ c) {N Q : ℕ}
    (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim N Q) (off i : ℕ) : _root_.ThreeSumApsp.WordRam.output c off i = μ (off + i) := by
  rw [_root_.ThreeSumApsp.WordRam.output, ← Nat.cast_add, h.rep]
  exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.toInt_wd (hfit.inRange (h.bounded _))

end run

/-! ## Solvers -/

/-- **The compiled program solves the problem on the word RAM**, within C · T + C steps, C depending
on the compiled program only. -/
theorem solves_of_programSolves {prob : _root_.ThreeSumApsp.WordRam.Problem} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p0 : ℕ} {dec : Bool} {s k r : ℕ}
    {dom : prob.Inst → Prop} {T : prob.Inst → ℝ} (h : _root_.ThreeSum1960614.Machine.Light.ProgramSolves prob P p0 dec s k dom T)
    (hr : ∀ x, (prob.params x).length ≤ r) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves prob (_root_.ThreeSum1960614.Machine.Light.compileProgram P p0 dec) (_root_.ThreeSum1960614.Machine.Light.slopeOf P dec s k r) dom
      fun x => (_root_.ThreeSum1960614.Machine.Light.timeConst P dec : ℝ) * T x + _root_.ThreeSum1960614.Machine.Light.timeConst P dec := by
  intro x hx W hadm
  obtain ⟨lim, σ', c, h⟩ := h x hx
  have hfit := _root_.ThreeSum1960614.Machine.Light.fits_of_small P dec h.small hadm (hr x) le_rfl
  obtain ⟨cfg, hrun, out⟩ :=
    _root_.ThreeSum1960614.Machine.Light.Compiler.compileProgram_correct h.run hfit (_root_.ThreeSum1960614.Machine.Light.input_loadWords W h.small.nonneg h.input_fits)
  refine ⟨_, _, cfg, _root_.ThreeSum1960614.Machine.Light.private_f79d03ee75_ramSteps_le_of_le P dec h.time, hrun, ?_⟩
  rw [show _root_.ThreeSumApsp.WordRam.output cfg (prob.input x).length = fun i => σ'.mem ((prob.input x).length + i) from
    funext (out.holds.output hfit _)]
  exact h.answer

/-! ## The two-stage data structure -/















/-! ## Absorbing the additive constant -/







end Light

end

end ThreeSum1960614.Machine

section
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.ThreeSum1960614.Machine.Light.Wrap

variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}
section

/-- **If the task is solved in time T, the problem is solved on the word RAM within a constant times
T.** -/
theorem ThreeSum1960614.Machine.Light.Wrap.realized__implementation_ebf05bdbf2 (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) {T : ℕ → ℝ → ℝ} (h : _root_.ThreeSum1960614.Machine.Light.SolvedIn task T) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Realized Q T := by
  obtain ⟨P, p, Tn, need, hpoly, hsol, hT⟩ := h
  intro κ
  obtain ⟨s, k, htop⟩ := w.topSolves hpoly hsol hT κ
  refine ⟨_, _, (_root_.ThreeSum1960614.Machine.Light.timeConst (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) dec : ℝ) * (w.extra κ + 1),
    by positivity,
    (_root_.ThreeSum1960614.Machine.Light.solves_of_programSolves htop (r := 1) fun x => by simp).mono le_rfl (fun _ hx => hx)
      fun x _ => ?_⟩
  -- `K (T + E) + K ≤ K (E + 1) T + K (E + 1)` for `K, E, T ≥ 0`
  have hT0 : (0 : ℝ) ≤ max (T x.n x.U) 0 := le_max_right _ _
  have hK : (0 : ℝ) ≤ (_root_.ThreeSum1960614.Machine.Light.timeConst (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) dec : ℝ) := by positivity
  have hE : (0 : ℝ) ≤ (w.extra κ : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hK hE) hT0]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Wrap.realized__implementation_ebf05bdbf2) := (@ThreeSum1960614.Machine.Light.Wrap.realized__implementation_ebf05bdbf2)

#print axioms solution
