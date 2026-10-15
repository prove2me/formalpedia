-- Prove2me | solution 1 for ThreeSum1960614.Machine.Light.Wrap.topSolves
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:19.221218+00:00
-- url     : https://prove2.me/submissions/2e043afc-057a-40ed-838c-bde11bb10cad

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Wrap_body_ends
import Theorems.Thm_ThreeSum1960614_Machine_Light_Wrap_small

local instance platformRadixNonzero_45e185a3e7 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace Light.Wrap
end Light.Wrap
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Wrap
end ThreeSum1960614.Machine.Light.Wrap
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
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/















theorem Ends.ite {σ T c s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hv he, by omega, hq⟩













/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/























/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.ite _ hs h₁ h₂ (by omega)





/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : _root_.EndStatement.Problem} (x : _root_.ThreeSumApsp.WordRam.Bounded Q)

/-- Cell 0 holds the size. -/
theorem ofEnd_cell0 (loc : ℕ → ℤ) : (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.k 0)).val ⟨loc, _root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)⟩ = x.n := by
  simp [_root_.Light.memOf]

/-- All cells of the input are within the size and the bound. -/
theorem ofEnd_input_le : ∀ a ∈ (_root_.ThreeSumApsp.WordRam.ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · rw [abs_of_nonneg (by positivity)]
    push_cast
    omega
  · have := _root_.ThreeSumApsp.WordRam.Bounded.abs_le ha
    push_cast
    omega

/-- Cell 0 may be read. -/
theorem safe_cell0 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {σ : _root_.ThreeSum1960614.Machine.Light.State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) :
    (_root_.ThreeSum1960614.Machine.Light.M (_root_.ThreeSum1960614.Machine.Light.k 0)).Safe lim σ := by
  (simp only [_root_.ThreeSum1960614.Machine.Light.Expr.Safe, _root_.ThreeSum1960614.Machine.Light.Expr.val, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.Light.Op.eval, _root_.ThreeSum1960614.Machine.Light.Cond.Holds, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Cond.Safe, _root_.Function.update_apply, _root_.reduceIte, _root_.true_and, _root_.and_true, _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat, _root_.Nat.cast_zero, _root_.Nat.cast_one, ])
  exact ⟨h0, le_rfl, by omega⟩

end OfEnd

/-! ## Polynomials in the size -/





namespace Wrap
open _root_.Light.Wrap


variable {Q : _root_.EndStatement.Problem} {task : _root_.Light.Task} {dec : Bool}









/-- The limits of the run leave that room. -/
theorem room (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need) (x : _root_.ThreeSumApsp.WordRam.Bounded Q) :
    w.Room need x (w.limits need x) := by
  have hfr := w.fr_pos x
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp only [_root_.ThreeSum1960614.Machine.Light.Wrap.limits] <;> omega





/-- The run of the outermost procedure on an instance of size 0. -/
theorem body_ends_zero (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p κ : ℕ) (x : _root_.ThreeSumApsp.WordRam.Bounded Q) (hn : x.n = 0)
    {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} (hroom : w.Room need x lim) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) 1 (_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec)
      ⟨_root_.Light.frame [0, 0], _root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)⟩ 9 (_root_.ThreeSum1960614.Machine.Light.Wrap.Answered x dec) := by
  have hbound := hroom.bound
  push_cast at hbound
  unfold _root_.ThreeSum1960614.Machine.Light.topBody
  -- n := mem[0]
  refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (x.n : ℤ) ?_ ⟨_root_.ThreeSum1960614.Machine.Light.safe_cell0 (by omega) hroom.space, _root_.ThreeSum1960614.Machine.Light.ofEnd_cell0 x _⟩
  -- if n ≠ 0 … else result := 0 or 1
  refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [hn]) h)
  have hanswer := w.zero x hn
  cases dec <;>
    exact _root_.ThreeSum1960614.Machine.Light.Ends.set (by simp; omega) (by (first
                                                                              | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                  first
                                                                                  | omega
                                                                                  | (ring_nf; omega))
                                                                              | omega
                                                                              |
                                                                                (simp [] <;>
                                                                                    first
                                                                                    | omega
                                                                                    | (ring_nf; omega)))) (by simpa [_root_.ThreeSum1960614.Machine.Light.Wrap.Answered, _root_.Light.verdictOf] using hanswer _)

/-- The outermost call, from the run of its procedure. -/
theorem ends_of_body (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) {P : _root_.ThreeSum1960614.Machine.Light.Program} {p κ T : ℕ} (x : _root_.ThreeSumApsp.WordRam.Bounded Q)
    {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends (w.limits need x) (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) 1 (_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec)
      ⟨_root_.Light.frame [0, 0], _root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)⟩ T (_root_.ThreeSum1960614.Machine.Light.Wrap.Answered x dec)) :
    _root_.ThreeSum1960614.Machine.Light.Ends (w.limits need x) (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt P.length)
      ⟨_root_.Light.frame [0, 0, 0], _root_.Light.memOf ((_root_.ThreeSumApsp.WordRam.ofEnd Q).input x)⟩ (T + 4) (_root_.ThreeSum1960614.Machine.Light.Wrap.Answered x dec) :=
  _root_.ThreeSum1960614.Machine.Light.Ends.call T (by simp) (by simp) (by simp only [_root_.ThreeSum1960614.Machine.Light.Wrap.limits]; omega)
    (h.mono le_rfl fun _ hσ => by simpa [_root_.ThreeSum1960614.Machine.Light.Wrap.Answered] using hσ) (by (first
                                                                                                            | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                                first
                                                                                                                | omega
                                                                                                                | (ring_nf; omega))
                                                                                                            | omega
                                                                                                            |
                                                                                                              (simp [] <;>
                                                                                                                  first
                                                                                                                  | omega
                                                                                                                  | (ring_nf; omega))))







end Wrap

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

/-- The compiled program is run within these limits: what the interface to the machine asks for. -/
theorem ThreeSum1960614.Machine.Light.Wrap.topSolves__implementation_7727cce274 (w : _root_.ThreeSum1960614.Machine.Light.Wrap Q task dec) {T : ℕ → ℝ → ℝ} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need} (hpoly : _root_.ThreeSum1960614.Machine.Light.PolyNeed need) (hsol : _root_.ThreeSum1960614.Machine.Light.Solves task P p Tn need)
    (hT : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u) (κ : ℕ) :
    ∃ s k : ℕ, _root_.ThreeSum1960614.Machine.Light.ProgramSolves (_root_.ThreeSumApsp.WordRam.ofEnd Q) (P ++ [_root_.ThreeSum1960614.Machine.Light.topBody κ p w.args dec]) P.length dec s k
      (fun x => x.U = x.n ^ κ) fun x => max (T x.n x.U) 0 + w.extra κ := by
  obtain ⟨s, k, hsmall⟩ := w.small hpoly κ
  refine ⟨s, k, fun x hU => ?_⟩
  have hinput : ∀ a ∈ (_root_.ThreeSumApsp.WordRam.ofEnd Q).input x, |a| ≤ (w.limits need x).word := fun a ha =>
    (_root_.ThreeSum1960614.Machine.Light.ofEnd_input_le x a ha).trans (by simp only [_root_.ThreeSum1960614.Machine.Light.Wrap.limits]; omega)
  rcases Nat.eq_zero_or_pos x.n with hn | hn
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends_zero P p κ x hn (w.room need x))
    have hc' : (c : ℝ) ≤ w.extra κ := by exact_mod_cast hc.trans (by unfold _root_.ThreeSum1960614.Machine.Light.Wrap.extra _root_.ThreeSum1960614.Machine.Light.Wrap.bodySteps; omega)
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_right (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
  · obtain ⟨σ', c, hrun, hc, hanswer⟩ :=
      w.ends_of_body x (w.body_ends hsol κ x hn hU (w.room need x))
    have hc' : (c : ℝ) ≤ (Tn x.n x.U : ℝ) + w.extra κ := by
      exact_mod_cast hc.trans (by unfold _root_.ThreeSum1960614.Machine.Light.Wrap.extra; omega)
    have hTn := hT x.n x.U x.U hn (hU ▸ Nat.one_le_pow _ _ hn) le_rfl
    exact ⟨w.limits need x, σ', c, hrun, by linarith [le_max_left (T x.n x.U) 0], hinput,
      hsmall x hU, hanswer⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.Light.Wrap.topSolves__implementation_7727cce274) := (@ThreeSum1960614.Machine.Light.Wrap.topSolves__implementation_7727cce274)

#print axioms solution
